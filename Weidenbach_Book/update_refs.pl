#! /usr/bin/perl
use strict;
use warnings;
use File::Find;
use Getopt::Long;


#the directory where to look for the .aux file
my $cw_book = "/home/zmaths/ENS/CWBook/Source/Chapters";

#the directory where to find the .thy files
my $thys_dir = "/home/zmaths/ENS/isafol/Weidenbach_Book";

#unsafe copy
my $unsafe = 0;
my $verbose = 0;
my $result = GetOptions ("unsafe"  => \$unsafe,
    "verbose" => \$verbose);  # flag

print "unsafe mode: $unsafe";

#hash table from the reference to the properties
my $numbers_of_label;

#the properties
my $page_number = "page"; # fudge
my $thm = "theorem"; # fudge
my $full_name = "full_name"; # Fudge


#parse the .aux and update the hashing 
sub read_file {
    my $name = $_;
    if (not ($name =~ /.*\.aux/)) {
	return
    }
    open my $fh, $File::Find::name or die "cannot open $name";
    print "starting parsing file $name\n";
    while (my $line = <$fh>) {
	if ($line =~ /\\newlabel\{([^\}]*)\}\{\{([^\}]*)\}\{([^\}]*)\}\{([^\}]*)\}\{([^\}\.]*)[^\}]*\}\{([^\}])*\}\}/ ) {
	    #example of parsed line: \newlabel{sec:prop:applications:sudoku}{{2.14.1}{109}{Sudoku}{subsection.2.14.1}{}}
	    #sanitizing input
	    my $l = $1; $l //= "";
	    my $a = $2; $a //= "";
	    my $p = $3; $p //= "";
	    my $t = $4; $t //= "";
	    my $n = $5; $n //= "";
	    my $o = $6; $o //= "";
	    if ($numbers_of_label->{$l}){
		warn "multiple defined $l, previously with reference $numbers_of_label->{$l}->{$full_name}\n" 
	    }
	    $numbers_of_label->{$l} = {$page_number => $a, $thm => $p, $full_name => "$n $a page $p"};
	}
    }

    close $fh;
}


sub parse_file_and_replace {
    my $name = $_;
    my $output = "{$name}2";
    if (not ($name =~ /.*\.thy$/)) {
	return
    }
    open my $fh, $File::Find::name or die "cannot open $name";
    open my $fout, '>', "$File::Find::dir/$name"."2" or die "cannot open $File::Find::dir/$name"."2";
    while (my $line = <$fh>) {
	my $old_line = $line;
	$line =~ /\\cwref\{([^\}]*)\}\{[^\}]*\}/;
	my $l = $1; $l //= "";
	if ($numbers_of_label->{$l}){
	    $line =~ s/\\cwref\{([^\}]*)\}\{[^\}]*\}/\\cwref\{$l\}\{$numbers_of_label->{$l}->{$full_name}\}/g;

	    if($verbose or not $unsafe){
		print "replace \n\t $old_line\nby\n\t$line";	
	    }
	    
	}
	if ($unsafe) {
	    print $fout $line;
	}

    }

    if($unsafe) {
	rename("$File::Find::dir/$name"."2",$File::Find::name)
    }
}

sub print_all_keys_values() {
    while ( my ($key, $value) = each($numbers_of_label) ) {
	while ( my ($key2, $prop) = each($value) ) {
	    print "$key => $prop\n";
	}
    }
}



print "Hello World\n";

finddepth(\&read_file, $cw_book);
finddepth(\&parse_file_and_replace, $thys_dir);

#opendir(my $dir, $cw_book) || die "Can't open directory: $!\n";

#my @files = grep { /.*\.aux$/ } readdir $dir;

#print "\nopenning files: @files\n\n";

#foreach my $f (@files) {
#      print "\$f = $f\n";
#	read_file $f
#
#    
#}
#closedir($dir);


