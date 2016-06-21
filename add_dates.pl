#!/usr/bin/perl

use strict;
use warnings;
use File::Find;
use Getopt::Long;

use POSIX qw(strftime);


my $html_dir = "/Users/mfleury/Documents/repos/isafol/html/current";

my $unsafe = 0;
my $verbose = 0;
my $isabelle = "";
my $afp = "";
my $isafol = "";
my $result = GetOptions ("unsafe!"  => \$unsafe,
			 "verbose!" => \$verbose,
			 "isabelle=s" => \$isabelle,
			 "afp=s" => \$afp,
			 "isafol=s" => \$isafol,
			 "html=s" => \$html_dir);  # flag

my $date = strftime "%F", localtime;

my $full_date = strftime "%A, %d %B, %Y", localtime;

my $html_versions_output =
    "<div class=body>" .
    "<p>" . 
    "<table border=0  width=700> " .
    "<tr>" .
      "<th>Isabelle version:</th>" . 
      "<th>AFP version:</th>" . 
      "<th>IsaFoL version:</th>" .
      "<th>Last compilation:</th>" .
    "</tr>".
    "<tr>" .
      "<td align=\"center\">$isabelle </td>" . 
      "<td align=\"center\">$afp </td>" . 
      "<td align=\"center\">$isafol </td>" .
      "<td align=\"center\">$full_date </td>" .
    "</tr>" .
    "</table>" .
    "</p>" . 
    "</div>";
    
sub replace_unidentifier_repository_version {
    my $name = "$_";
    if (not ($name =~ /.*\.html$/)) {
	return
    }
    open my $fh, $File::Find::name or die "cannot open $name";
    open my $fout, '>', "$File::Find::dir/$name"."2" or die "cannot open $File::Find::dir/$name"."2";

    if ($verbose){
	print "starting parsing file $name\n";
    }
    
    while (my $line = <$fh>) {
	if ($line =~ /(.*)\(unidentified repository version\)(.*)/ ) {
	    my $title_begining = $1; $title_begining//= "";
	    my $title_end = $2; $title_end //= "";

	    $line =~ s/(unidentified repository version)/$date/g;
	    if($verbose) {
		print "title found: $title_begining $title_end\n";
		print "\tand replace by $line\n"
	    }
	}
	
	if ($line =~ /<\/h1>/ ) {

	    $line =~ s/<\/h1>/<\/h1>\n\n$html_versions_output/g;
	    if($verbose) {
		print "head found and replaced by $line\n"
	    }
	}
	
	print $fout $line
    }
    
    if($unsafe) {
	rename("$File::Find::dir/$name"."2",$File::Find::name)
    }
    close $fh;
}

finddepth(\&replace_unidentifier_repository_version, $html_dir);
