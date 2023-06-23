#!/usr/bin/perl -T


# dispgpgpub: this is a utility to display the RSA public key 
# components contained in a binary (i.e., not armored) gpg public
# key file. It is a heavily modified version of keytrans found in
# the monkeysphere project intended to be easy to read and understand
# for the purpose of display gpg RSA public key information.
# It is therefore covered by monkeyspehere's licensing (i.e., this 
# is GNU GPL v3 licensed). 
#
# Usage: takes a OpenPGP public key file as the first argument and
# emits its modulus and public export on stdout.

# Example usage:

# dispgpgpub pub_key.gpg


# Authors:
#  Jonathan Schulze-Hewett <schulze-hewett@infoseccorp.com>

# Original monkeysphere authors:
#  Jameson Rollins <jrollins@finestructure.net>
#  Daniel Kahn Gillmor <dkg@fifthhorseman.net>

# License: GPL v3 or later (we may need to adjust this given that this
# connects to OpenSSL via perl)

use strict;
use warnings;
use File::Basename;
use Crypt::OpenSSL::RSA;
use Crypt::OpenSSL::Bignum;
use Crypt::OpenSSL::Bignum::CTX;
use Digest::SHA;
use MIME::Base64;
use POSIX;

## make sure all length() and substr() calls use bytes only:
use bytes;

my $old_format_packet_lengths = { one => 0,
				  two => 1,
				  four => 2,
				  indeterminate => 3,
};

# see RFC 4880 section 9.1 (ignoring deprecated algorithms for now)
my $asym_algos = { rsa => 1,
		   elgamal => 16,
		   dsa => 17,
		   };

# see RFC 4880 section 9.2
my $ciphers = { plaintext => 0,
		idea => 1,
		tripledes => 2,
		cast5 => 3,
		blowfish => 4,
		aes128 => 7,
		aes192 => 8,
		aes256 => 9,
		twofish => 10,
	      };

# see RFC 4880 section 9.3
my $zips = { uncompressed => 0,
	     zip => 1,
	     zlib => 2,
	     bzip2 => 3,
	   };

# see RFC 4880 section 9.4
my $digests = { md5 => 1,
		sha1 => 2,
		ripemd160 => 3,
		sha256 => 8,
		sha384 => 9,
		sha512 => 10,
		sha224 => 11,
	      };

# see RFC 4880 section 5.2.3.21
my $usage_flags = { certify => 0x01,
		    sign => 0x02,
		    encrypt_comms => 0x04,
		    encrypt_storage => 0x08,
		    encrypt => 0x0c, ## both comms and storage
		    split => 0x10, # the private key is split via secret sharing
		    authenticate => 0x20,
		    shared => 0x80, # more than one person holds the entire private key
		  };

# see RFC 4880 section 4.3
my $packet_types = { pubkey_enc_session => 1,
		     sig => 2,
		     symkey_enc_session => 3,
		     onepass_sig => 4,
		     seckey => 5,
		     pubkey => 6,
		     sec_subkey => 7,
		     compressed_data => 8,
		     symenc_data => 9,
		     marker => 10,
		     literal => 11,
		     trust => 12,
		     uid => 13,
		     pub_subkey => 14,
		     uat => 17,
		     symenc_w_integrity => 18,
		     mdc => 19,
		   };

# see RFC 4880 section 5.2.1
my $sig_types = { binary_doc => 0x00,
		  text_doc => 0x01,
		  standalone => 0x02,
		  generic_certification => 0x10,
		  persona_certification => 0x11,
		  casual_certification => 0x12,
		  positive_certification => 0x13,
		  subkey_binding => 0x18,
		  primary_key_binding => 0x19,
		  key_signature => 0x1f,
		  key_revocation => 0x20,
		  subkey_revocation => 0x28,
		  certification_revocation => 0x30,
		  timestamp => 0x40,
		  thirdparty => 0x50,
		};


# see RFC 4880 section 5.2.3.23
my $revocation_reasons = { no_reason_specified => 0,
			   key_superseded => 1,
			   key_compromised => 2,
			   key_retired => 3,
			   user_id_no_longer_valid => 32,
			 };

# see RFC 4880 section 5.2.3.1
my $subpacket_types = { sig_creation_time => 2,
			sig_expiration_time => 3,
			exportable => 4,
			trust_sig => 5,
			regex => 6,
			revocable => 7,
			key_expiration_time => 9,
			preferred_cipher => 11,
			revocation_key => 12,
			issuer => 16,
			notation => 20,
			preferred_digest => 21,
			preferred_compression => 22,
			keyserver_prefs => 23,
			preferred_keyserver => 24,
			primary_uid => 25,
			policy_uri => 26,
			usage_flags => 27,
			signers_uid => 28,
			revocation_reason => 29,
			features => 30,
			signature_target => 31,
			embedded_signature => 32,
			issuer_fpr => 33,
		       };

# bitstring (see RFC 4880 section 5.2.3.24)
my $features = { mdc => 0x01
	       };

# bitstring (see RFC 4880 5.2.3.17)
my $keyserver_prefs = { nomodify => 0x80
		      };

###### end lookup tables ######


# pull an OpenPGP-specified MPI off of a given stream, returning it as
# a Crypt::OpenSSL::Bignum.
sub read_mpi {
  my $instr = shift;
  my $readtally = shift;

  my $bitlen;
  read($instr, $bitlen, 2) or die "could not read MPI length.\n";
  $bitlen = unpack('n', $bitlen);
  $$readtally += 2;

  my $bytestoread = POSIX::floor(($bitlen + 7)/8);
  my $ret;
  read($instr, $ret, $bytestoread) or die "could not read MPI body.\n";
  $$readtally += $bytestoread;
  return Crypt::OpenSSL::Bignum->new_from_bin($ret);
}

# FIXME: handle non-RSA keys

# given an input stream and data, store the found key in data and
# consume the rest of the stream corresponding to the packet.
# data contains: (fpr: fingerprint to find, key: current best guess at key)
sub findkey {
  my $data = shift;
  my $instr = shift;
  my $tag = shift;
  my $packetlen = shift;

  my $dummy;
  my $ver;
  my $readbytes = 0;

  read($instr, $ver, 1) or die "could not read key version\n";
  $readbytes += 1;
  $ver = ord($ver);

  if ($ver != 4) {
    printf(STDERR "We only work with version 4 keys.  This key appears to be version %s.\n", $ver);
    read($instr, $dummy, $packetlen - $readbytes) or die "Could not skip past this packet.\n";
    return;
  }

  my $key_timestamp;
  read($instr, $key_timestamp, 4) or die "could not read key timestamp.\n";
  $readbytes += 4;
  $key_timestamp = unpack('N', $key_timestamp);

  my $algo;
  read($instr, $algo, 1) or die "could not read key algorithm.\n";
  $readbytes += 1;
  $algo = ord($algo);
  if ($algo != $asym_algos->{rsa}) {
    printf(STDERR "We only support RSA keys (this key used algorithm %d).\n", $algo);
    read($instr, $dummy, $packetlen - $readbytes) or die "Could not skip past this packet.\n";
    return;
  }

  ## we have an RSA key.
  my $modulus = read_mpi($instr, \$readbytes);
  my $exponent = read_mpi($instr, \$readbytes);

  my $pubkey = Crypt::OpenSSL::RSA->new_key_from_parameters($modulus, $exponent);

  $data->{key} = { 'rsa' => $pubkey,
		     'timestamp' => $key_timestamp };
  $data->{current_key_match} = 1;

  return;  
}

sub openpgp2rsa {
  my $instr = shift;



  my $data = { };
  my $subs = { $packet_types->{pubkey} => \&findkey,
	       $packet_types->{pub_subkey} => \&findkey};

  packetwalk($instr, $subs, $data);

  return $data->{key}->{rsa};
}



sub packetwalk {
  my $instr = shift;
  my $subs = shift;
  my $data = shift;

  my $packettag;
  my $dummy;
  my $tag;

  while (! eof($instr)) {
    read($instr, $packettag, 1);
    $packettag = ord($packettag);

    my $packetlen;
    if ( ! (0x80 & $packettag)) {
      die "This is not an OpenPGP packet\n";
    }
    if (0x40 & $packettag) {
      # this is a new-format packet.
      $tag = (0x3f & $packettag);
      my $nextlen = 0;
      read($instr, $nextlen, 1);
      $nextlen = ord($nextlen);
      if ($nextlen < 192) {
	$packetlen = $nextlen;
      } elsif ($nextlen < 224) {
	my $newoct;
	read($instr, $newoct, 1);
	$newoct = ord($newoct);
	$packetlen = (($nextlen - 192) << 8) + ($newoct) + 192;
      } elsif ($nextlen == 255) {
	read($instr, $nextlen, 4);
	$packetlen = unpack('N', $nextlen);
      } else {
	# packet length is undefined.
      }
    } else {
      # this is an old-format packet.
      my $lentype;
      $lentype = 0x03 & $packettag;
      $tag = ( 0x3c & $packettag ) >> 2;
      if ($lentype == 0) {
	read($instr, $packetlen, 1) or die "could not read packet length\n";
	$packetlen = unpack('C', $packetlen);
      } elsif ($lentype == 1) {
	read($instr, $packetlen, 2) or die "could not read packet length\n";
	$packetlen = unpack('n', $packetlen);
      } elsif ($lentype == 2) {
	read($instr, $packetlen, 4) or die "could not read packet length\n";
	$packetlen = unpack('N', $packetlen);
      } else {
	# packet length is undefined.
      }
    }

    if (! defined($packetlen)) {
      die "Undefined packet lengths are not supported.\n";
    }

    if (defined $subs->{$tag}) {
      $subs->{$tag}($data, $instr, $tag, $packetlen);
    } else {
      read($instr, $dummy, $packetlen) or die "Could not skip past this packet!\n";
    }
  }

  return $data->{key};
}

sub begins_with
{
    return substr($_[0], 0, length($_[1])) eq $_[1];
}

for (basename($0)) {
      if ($#ARGV + 1 != 1) {
          die "Usage: ".basename($0)." gpg_public_key.gpg\n";
      }
      my $infile = shift;
      my $instream;
      # read whole thing into memory
      open($instream,$infile);
      binmode($instream, ":bytes");
      read $instream, my $file_content, -s $instream;

      # if it is ascii armor'd turn it into binary data
      if (begins_with($file_content, "-----")) {
          my @splitstr = split('\n\n', $file_content);
          $file_content = $splitstr[1];
          $file_content = decode_base64($file_content);
      }
      
      # open the string as a stream
      open(my $fh, "<", \$file_content);

      # get the public key out
      my $key = openpgp2rsa($fh);
      if (defined($key)) {
	if ($key->is_private()) {
	  die "Private keys are not supported.\n";
	} else {
          my ($modulus, $exponent) = $key->get_key_parameters();
	  print "Modulus:  ".$modulus->to_hex."\n";
          print "Exponent: ".$exponent->to_hex."\n";
	}
      } else {
	die "No matching key found.\n";
      }
}

