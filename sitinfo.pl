#!/usr/local/bin/perl -w
#------------------------------------------------------------------------------
# Licensed Materials - Property of IBM (C) Copyright IBM Corp. 2010, 2010
# All Rights Reserved US Government Users Restricted Rights - Use, duplication
# or disclosure restricted by GSA ADP Schedule Contract with IBM Corp
#------------------------------------------------------------------------------

#  perl sitinfo.pl
#
#  Report Situation Distribution
#
#  john alvord, IBM Corporation, 10 July 2014
#  jalvord@us.ibm.com
#
# tested on Windows Activestate 5.16.2
# Should work on Linux/Unix but not yet tested
#
# $DB::single=2;   # remember debug breakpoint
#     use re 'debug';
## todos

#use warnings::unused; # debug used to check for unused variables
use strict;
use warnings;

# See short history at end of module

my $gVersion = "0.80000";
my $gWin = (-e "C://") ? 1 : 0;    # 1=Windows, 0=Linux/Unix

use Data::Dumper;               # debug only

# a collection of variables which are used throughout the program.
# defined globally

my $args_start = join(" ",@ARGV);      # capture arguments for later processing
my $run_status = 0;                    # A count of pending runtime errors - used to allow multiple error detection before stopping process

# some common variables

my $rc;
my $node;
my $myargs;
my $survey_sqls = 0;                     # count of SQLs
my $survey_sql_time = 0;                 # record total elapsed time in SQL processing
my @words = ();
my $rt;
my $debugfile;
my $ll;
my $pcount;
my $oneline;
my $sx;
my @connections = ();                    # list of possible hub TEMS servers
my $connection="";                       # connection chosen to primary hub TEMS
my $key;
my $n;

my %agtusex;

my %localhostx;

# forward declarations of subroutines

sub init;                                # read command line and ini file
sub logit;                               # queue one record to survey log
sub datadumperlog;                       # dump a variable using Dump::Data if installed
sub gettime;                             # get time
sub init_txt;                            # input from txt files
sub init_lst;                            # input from lst files
sub newsit;                              # create new situation entry
sub newagt;                              # create new agemt entry
sub newlst;                              # create new TNODELST MSL entry
sub sitgroup_get_sits;                   # recursive sitgroup exploration
sub parse_lst;                           # parse the KfwSQLClient output


# Situation Group related data
my $gx;
my $grpi = -1;
my @grp = ();
my %grpx = ();
my @grp_name = ();
my @grp_sit = ();
my @grp_grp = ();
my %sum_sits = ();

my %sitfullx = ();                        # Index from situation index to Fullname

# Situation related data

my $siti = -1;                             # count of situations
my $curi;                                  # global index for subroutines
my @sit = ();                              # array of situations
my %sitx = ();                             # Index from situation name to index
my @sit_pdt = ();                          # array of predicates or situation formula
my @sit_fullname = ();                     # array of fullname
my @sit_psit = ();                         # array of printable situaton names
my @sit_sitinfo = ();                      # array of SITINFO columns
my @sit_autostart = ();                    # array of AUTOSTART columns
my @sit_sum = ();                          # count of *SUM
my @sit_agents = ();                       # Agents where this situation should run
my @sit_agenth = ();                       # hash of agent distribution
my @sit_dist = ();                         # When 1, distributed
my @sit_dist_objaccl = ();                 # Situation Distributions in TOBJACCL and TGROUP/TGROUPI
my @sit_reeval = ();                       # Situaton Sampling Interval
my @sit_text = ();                         # Situaton Description
my $sit_distribution = 0;                  # when 1, distributions are present


my %sitax;

my $agti = -1;
my @agt = ();
my %agtx = ();
my @agt_hostinfo = ();
my @agt_version = ();
my @agt_hostaddr = ();

my $lnodli = -1;
my @lnodl = ();
my %lnodlx = ();
my @lnodl_agent_ct = ();
my @lnodl_sit_ct = ();
my @lnodl_cal_ct = ();
my @lnodl_ovr_ct = ();
my @lnodl_pcy_ct = ();
my @lnodl_off_ct = ();
my @lnodl_nodes = ();

my $obji = -1;
my @obj = ();
my %objx = ();
my @obj_dist = ();

# option and ini file variables variables

my $opt_txt;                    # input from .txt files
my $opt_txt_tsitdesc;           # TSITDESC txt file
my $opt_txt_tname;              # TNAME txt file
my $opt_txt_tobjaccl;           # TOBJACCL txt file
my $opt_txt_tgroup;             # TGROUP txt file
my $opt_txt_tgroupi;            # TGROUPI txt file
my $opt_txt_tnodesav;           # TNODESAV txt file
my $opt_txt_tnodelst;           # TNODELST txt file
my $opt_txt_tcalendar;          # TCALENDAR txt file
my $opt_txt_toverride;          # TOVERRIDE txt file
my $opt_txt_tpcydesc;           # TPCYDESC txt file
my $opt_lst;                    # input from .lst files
my $opt_lst_tsitdesc;           # TSITDESC lst file
my $opt_lst_tsitdesc1;          # TSITDESC1 lst file
my $opt_lst_tsitdesc2;          # TSITDESC2 lst file
my $opt_lst_tname;              # TNAME lst file
my $opt_lst_tobjaccl;           # TOBJACCL txt file
my $opt_lst_tgroup;             # TGROUP lst file
my $opt_lst_tgroupi;            # TGROUPI lst file
my $opt_lst_tnodesav;           # TNODESAV lst file
my $opt_lst_tnodelst;           # TNODELST lst file
my $opt_lst_tcalendar;          # TCALENDAR lst file
my $opt_lst_toverride;          # TOVERRIDE lst file
my $opt_lst_tpcydesc;           # TPCYDESC lst file
my $opt_log;                    # name of log file
my $opt_ini;                    # name of ini file
my $opt_debuglevel;             # Debug level
my $opt_debug;                  # Debug level
my $opt_h;                      # help file
my $opt_v;                      # verbose flag
my $opt_vt;                     # verbose traffic flag
my $opt_dpr;                    # dump data structure flag
my $opt_std;                    # Credentials from standard input
my $opt_o;                      # output file
my $opt_workpath;               # Directory to store output files
my $opt_runall;                 # check Run at Startup = *OFF situations
my $opt_syntax;                 # syntax tracing
my $opt_zero = 0;               # show situations with zero distribution
my $opt_onerow = 0;             # show situations with one row per agent
my $opt_remove = 0;             # generate remove.sh and remove.cmd for unused MSLs
my $opt_remove_cmd = "remove.cmd";  # remove file name for Windows
my $opt_remove_sh = "remove.sh";    # remove file name for Linux/Unix

my %calex;
my %overx;
my %pcyfx;

# do basic initialization from parameters, ini file and standard input

$rc = init($args_start);

$opt_log = $opt_workpath . $opt_log;
open FH, ">>$opt_log" or die "can't open $opt_log: $!";

logit(0,"SITINFO000I - ITM_Situation_Information $gVersion $args_start");

# process two different sources of situation data

if ($opt_txt == 1) {                    # text files
   $rc = init_txt();
} elsif ($opt_lst == 1) {               # KfwSQLClient LST files
   $rc = init_lst();
}


open OH, ">$opt_o" or die "can't open csv file $opt_o: $!";
print OH "Situation Distribution Information Report $gVersion\n";
print OH "\n";
print OH "Limited to situations with Run at Startup and distributed to at least one known agent\n" if $opt_zero == 0;
print OH "Limited to situations with Run at Startup and including situations distributed to no agents\n" if $opt_zero == 1;
print OH "\n";
if ($opt_onerow == 0) {
   print OH "Situation,Severity,Agent_count,Agents,Predicate\n";
} else {
   print OH "Situation[Fullname],Severity,IP_Address,Agent,Why,Persist,Description,Reeval,Predicate\n";
}



my $sitone;
my $psitone;
my $sevone;
my $ipersist;
my $agent_ct;
my @hashsit = ();
my %disthash;

for (my $i=0;$i<=$siti;$i++) {
#print "$i\n";
   $sitone = $sit[$i];
   $psitone = $sit[$i];
   $psitone = $sit_fullname[$i] if $sit_fullname[$i] ne "";


   $sevone = "";
   $ipersist = "";
   if ($sit_sitinfo[$i] ne "") {
      $sit_sitinfo[$i] =~ /SEV=([^;]+)/;
      $sevone = $1 if defined $1;
   }
   if ($sit_sitinfo[$i] ne "") {
      $sit_sitinfo[$i] =~ /COUNT=([^;]+)/;
      $ipersist = $1 if defined $1;
   }
   $agent_ct =  scalar(keys %{$sit_agenth[$i]});
   if ($opt_zero == 0) {
      next if $agent_ct == 0;
   }
   my $agents = join(" ",keys %{$sit_agenth[$i]});
   push @hashsit,{sitname => $psitone,
                  pdt => $sit_pdt[$i],
                  severity => $sevone,
                  agent_ct => $agent_ct,
                  agent_reason => \%{$sit_agenth[$i]},
                 };

   my $oline = "";
   if ($opt_onerow == 0) {
      $oline = "";
      $oline .= $psitone . ",";
      $oline .= $sevone . ",";
      $oline .= $agent_ct . ",";
      $oline .= $agents . ",";
      $oline .= $sit_pdt[$i] . ",";
      print OH "$oline\n";
   } else {
      my %onerow = %{$sit_agenth[$i]};
      foreach my $f ( sort { $onerow{$a} cmp  $onerow{$b} } keys %onerow ) {
         $oline = "";
         $oline .= $sitone;
         if (defined $sitfullx{$sitone}) {
            $oline .= "[" . $sitfullx{$sitone} . "]";
         }
         $oline .= ",";

         $oline .= $sevone . ",";
         my $pip = "";
         my $ax = $agtx{$f};
         if (defined $ax) {
            my $hostaddr = $agt_hostaddr[$ax];
            if (index($hostaddr,":") != -1){
               $hostaddr =~ /:(.+)\[/;
               $pip = substr($1,1) if defined $1;
            }
         }
         $localhostx{$f} = 1 if $pip eq "127.0.0.1";
         $oline .= $pip . ",";
         $oline .= $f . ",";
         my $pwhy = "";
         my $why_ct = 0;
         $sx = $sitx{$sitone};
         $oline .= $pwhy . "," if !defined $sx;
         if (defined $sx) {
           my $why = $sit_agenth[$sx]{$f};
           foreach my $arr (@$why[0]) {
              foreach my $arr1 (@$arr) {
                 $pwhy .= @$arr1[0] . "|";
                 $pwhy .= @$arr1[1];
                 $pwhy .= "|" .  @$arr1[2] . ";" if defined @$arr1[2];
                 $pwhy .= ";" if !defined @$arr1[2];
                 $why_ct += 1;
              }
           }
           $oline .= $pwhy . ",";
         }
         $oline .= $ipersist . ",";
         $oline .= $sit_text[$i] . ",";
         $oline .= $sit_reeval[$i] . ",";
         $oline .= $sit_pdt[$i] . ",";
         print OH "$oline\n";

         my $agtuse_ref = $agtusex{$f};
         if (!defined $agtuse_ref) {
            my %agtuseref = (
                               count => 0,
                               pure => 0,
                               samp => 0,
                               samp_hr => 0,
                               sits => {},
                            );
            $agtuse_ref = \%agtuseref;
            $agtusex{$f} = \%agtuseref;
         }
         $agtuse_ref->{count} += 1;
         if ($sit_reeval[$i] == 0) {
            $agtuse_ref->{pure} += 1;
         } else {
            $agtuse_ref->{samp} += 1;
            $agtuse_ref->{samp_hr} += (3600/$sit_reeval[$i]);
         }
         my $isit = $sit[$i] . "|" . $sit_fullname[$i];
         $agtuse_ref->{sits}{$isit} = 1;
      }
   }
}
if ($opt_onerow == 1) {
   my $oline = "";
   print OH "\n";
   print OH "Agents with situation workload more than 120 samples per hour\n";
   print OH "Agents,Count,Pure,Samp,Samp/hr\n";
   foreach my $f ( sort { $agtusex{$b}->{samp_hr} cmp  $agtusex{$a}->{samp_hr}} keys %agtusex ) {
      my $agtuse_ref = $agtusex{$f};
      last if $agtuse_ref->{samp_hr} <= 120;
      $oline = $f . ",";
      $oline .= $agtuse_ref->{count} . ",";
      $oline .= $agtuse_ref->{pure} . ",";
      $oline .= $agtuse_ref->{samp} . ",";
      $oline .= $agtuse_ref->{samp_hr} . ",";
      print OH "$oline\n";
   }
}

if ($opt_runall == 1) {
   print OH "\n";
   print OH "MSLs with only non-autostart situations\n";
   print OH "\n";
   for (my $i=0;$i<=$lnodli;$i++) {
     my $lnodl1 = $lnodl[$i];
     next if $lnodl_sit_ct[$i] > 0;
     next if $lnodl_cal_ct[$i] > 0;
     next if $lnodl_ovr_ct[$i] > 0;
     next if $lnodl_pcy_ct[$i] > 0;
     next if $lnodl_off_ct[$i] == 0;
     next if substr($lnodl1,0,1) eq "*";
     print OH "$lnodl1,$lnodl_off_ct[$i],\n";
  }
}




if ($opt_remove == 1) {
   open CMD, ">$opt_remove_cmd" or die "can't open $opt_remove_cmd: $!";
   open SH, ">$opt_remove_sh" or die "can't open $opt_remove_sh: $!";
   binmode(SH);
}
my $total_unused_msl_rows=0;
my $cmd_line;
print OH "\n";
print OH "Managed System Lists with no usage in direct distribution or indirect via Situation Groups or Calendar or Override or Policy\n";
print OH "MSL,Agents,\n";
for (my $i=0;$i<=$lnodli;$i++) {
  my $lnodl1 = $lnodl[$i];
  next if $lnodl_sit_ct[$i] > 0;
  next if $lnodl_cal_ct[$i] > 0;
  next if $lnodl_ovr_ct[$i] > 0;
  next if $lnodl_pcy_ct[$i] > 0;
  next if substr($lnodl1,0,1) eq "*";
  print OH "$lnodl1,$lnodl_agent_ct[$i]\n";
  $total_unused_msl_rows += $lnodl_agent_ct[$i];
  if ($opt_remove == 1) {
      $cmd_line = "tacmd deletesystemlist -l $lnodl1 -f\n";
      print CMD $cmd_line;
      print SH "./" . $cmd_line;
  }
}
print OH "unused_rows,$total_unused_msl_rows,\n";
if ($opt_remove == 1) {
   close(CMD);
   close(SH);
}

my $total_used_msl_rows=0;
print OH "\n";
print OH "Managed System Lists with usage in direct distribution or indirect via Situation Groups\n";
print OH "MSL,Agents,\n";
for (my $i=0;$i<=$lnodli;$i++) {
  my $lnodl1 = $lnodl[$i];
  next if $lnodl_sit_ct[$i] == 0;
  next if substr($lnodl1,0,1) eq "*";
  print OH "$lnodl1,$lnodl_agent_ct[$i]\n";
  $total_used_msl_rows += $lnodl_agent_ct[$i];
}
print OH "used_rows,$total_used_msl_rows,\n";

my $local_cnt = scalar(keys %localhostx);
if ($local_cnt > 0) {
   print OH "\n";
   print OH "Agents [$local_cnt] Registering Localhost 127.0.0.1 as system address\n";
   print OH "Agents,\n";
   foreach my $f ( sort { $a cmp  $b } keys %localhostx ) {
      print OH $f . ",\n";
   }
}

for (my $i=0;$i<=$siti;$i++) {
   my $agent_ct = scalar(@{$sit_agents[$i]});
   next if $agent_ct == 0;
   $sitax{$sit[$i]} += $agent_ct;
}

my  %sitar;
my $f;
print OH "\n";
print OH "Situations Distributed to Agents sorted by count,\n";
foreach $f (sort {$sitax{$b} <=> $sitax{$a}} keys %sitax) {
   print OH $f . "," . $sitax{$f} . "\n";
   $sitar{$sitax{$f}} += 1;
}

print OH "\n";
print OH "Number of agents Situations sorted by count,\n";
foreach $f (sort {$sitar{$b} <=> $sitar{$a}} keys %sitar) {
   print OH $f . "," . $sitar{$f} . "\n";
}


close OH;

exit;

# sitgroup_get_sits calculates the sum of all situations which are in this group or
# further groups in the DAG [Directed Acyclic Graph] that composes the
# situation groups. Result is returned in the global hash sum_sits which the caller manages.

# $grp_grp is an array
# $grp_grp[$base_node] is one scalar instance
# The instance is actually a hash of values, so we reference that by forcing it
#   %{$grp_grp[$base_node]} and that way the hash can be worked on.

sub sitgroup_get_sits
{
   my $base_node = shift;     # input index

   while( my ($refsit, $refval) = each %{$grp_sit[$base_node]}) {    # capture the situations into global hash.
      $sum_sits{$refsit} = 1;
      logit(100,"Sitgroup $refsit added from $grp[$base_node]");
   }
   while( my ($refgrp, $refval) = each %{$grp_grp[$base_node]}) {    # for groups, call recursively
      my $refgx = $grpx{$refgrp};
      next if !defined $refgx;
      logit(100,"Sitgroup seach entering $grp[$refgx] from $grp[$base_node]");
      sitgroup_get_sits($refgx);
   }
}

sub newlst {
      my ($ilnode,$ilnodelist) = @_;

      my $lx = $lnodlx{$ilnodelist};
      if (!defined $lx) {
         $lnodli += 1;
         $lnodl[$lnodli] = $ilnodelist;
         $lnodlx{$ilnodelist} = $lnodli;
         $lnodl_nodes[$lnodli] = ();
         $lnodl_agent_ct[$lnodli] = 0;
         $lnodl_sit_ct[$lnodli] = 0;
         $lnodl_cal_ct[$lnodli] = 0;
         $lnodl_ovr_ct[$lnodli] = 0;
         $lnodl_pcy_ct[$lnodli] = 0;
         $lnodl_off_ct[$lnodli] = 0;
         $lx = $lnodli;
      }
      $lnodl_agent_ct[$lx] += 1;
      push @{$lnodl_nodes[$lx]}, $ilnode;
}

sub newagt {
      my ($iagt,$ihostinfo,$iversion,$ihostaddr) = @_;
      $agti += 1;
      $agt[$agti] = $iagt;
      $agtx{$iagt} = $agti;
      $agt_hostinfo[$agti] = $ihostinfo;
      $agt_version[$agti] = $iversion;
      $agt_hostaddr[$agti] = $ihostaddr;
}

sub newsit {
      my ($isitname,$ipdt,$ifullname,$iautostart,$isitinfo,$ireev_days,$ireev_time) = @_;
      $siti += 1;
      $iautostart = "*NO" if $iautostart eq "";
      $sit[$siti] = $isitname;
      $sitx{$isitname} = $siti;
      $sit_psit[$siti] = $isitname;
      $sit_pdt[$siti] = $ipdt;
      $sit_fullname[$siti] = $ifullname;
      $sit_autostart[$siti] = $iautostart;
      $ireev_days += 0;
      my $reev_time_hh = 0;
      my $reev_time_mm = 0;
      my $reev_time_ss = 0;
      if ($ireev_time ne "0") {
         $reev_time_hh = substr($ireev_time,0,2);
         $reev_time_mm = substr($ireev_time,2,2);
         $reev_time_ss = substr($ireev_time,4,2);
      }
      $sit_reeval[$siti] = $ireev_days*86400+$reev_time_hh*3600+$reev_time_mm*60+$reev_time_ss;
      $sit_sitinfo[$siti] = $isitinfo;
      $sit_agents[$siti] = [];                      # Array of agents where situation should run
      $sit_agenth[$siti] = ();                      # hash of arrays of arrays concerning distribution of sits
      $sit_sum[$siti] = 0;
      $sit_dist[$siti] = 0;                         # When 1, there is a distribution
      $sit_dist_objaccl[$siti] = "";                # list of distributions
      $sit_text[$siti] = "";                        # Situation Desciption
}


# following routine gets data from txt files. tems2sql.pl is an internal only program which can
# extract data from a TEMS database file. The way it is used here the results are a fixed column
# orientation.

sub init_txt {
   my @kgrp_data;
   my @kgrpi_data;
   my @ksit_data;
   my @ktna_data;
   my @kobj_data;
   my @knod_data;
   my @klst_data;
   my @kcale_data;
   my @kovrd_data;
   my @kpcyf_data;
   my $isitname;
   my $ifullname;
   my $ipdt;
   my $iautostart;
   my $isitinfo;
   my $icmd;
   my $itext;
   my $ireev_days;
   my $ireev_time;
   my $iid;
   my $igrpclass;
   my $igrpname;
   my $iobjname;
   my $iobjclass;
   my $inodel;

   my $iagt;
   my $ihostinfo;
   my $iversion;
   my $ihostaddr;

   my $ilnode;
   my $ilnodelist;

   my $iname;

   # (1) the TGROUP data  - get a list of IDs and prepare slot of SITs and GRPs
   open(KGRP, "< $opt_txt_tgroup") || die("Could not open TGROUP $opt_txt_tgroup\n");
   @kgrp_data = <KGRP>;
   close(KGRP);

   # make an array of all group identifications
   $ll = 0;
   foreach $oneline (@kgrp_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $iid = substr($oneline,0,32);
      $iid =~ s/\s+$//;   #trim trailing whitespace
      $igrpclass = substr($oneline,33,4);
      next if $igrpclass ne '2010';
      $igrpname = substr($oneline,42,256);
      $igrpname =~ s/\s+$//;   #trim trailing whitespace
      $gx = $grpx{$iid};
      if (!defined $gx) {
         $grpi++;
         $gx = $grpi;
         $grp[$gx] = $iid;
         $grpx{$iid} = $gx;
         $grp_name[$gx] = $igrpname;
         $grp_sit[$gx] = {};
         $grp_grp[$gx] = {};
      }
   }

   # (2) the TGROUPI data
   open(KGRPI, "< $opt_txt_tgroupi") || die("Could not open TGROUPI $opt_txt_tgroupi\n");
   @kgrpi_data = <KGRPI>;
   close(KGRPI);

   # Work through all the group items
   $ll = 0;
   foreach $oneline (@kgrpi_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $iid = substr($oneline,0,32);
      $iid =~ s/\s+$//;   #trim trailing whitespace
      $iobjname = substr($oneline,33,32);
      $iobjname =~ s/\s+$//;   #trim trailing whitespace
      $iobjclass = substr($oneline,66,4);
      $igrpclass = substr($oneline,75,4);
      next if $igrpclass ne '2010';
      if (($iobjclass ne '5140') & ($iobjclass ne '2010')) {
         next;
      }
      $gx = $grpx{$iid};
      if (!defined $gx) {
         warn "unknown group id $iid in tgroupi $opt_txt_tgroupi $ll.\n";
         next;
      }
      $grp_sit[$gx]->{$iobjname} = 1 if $iobjclass eq '5140';
      $grp_grp[$gx]->{$iobjname} = 1 if $iobjclass eq '2010';
   }

   # (3) TNODELST data - M type which agent/nodelist data
   open(KLST, "< $opt_txt_tnodelst") || die("Could not open tnodelst $opt_txt_tnodelst\n");
   @klst_data = <KLST>;
   close(KLST);

   $ll = 0;
   foreach $oneline (@klst_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      next if substr($oneline,0,1) ne "M";
      $ilnode = substr($oneline,9,32);
      $ilnode =~ s/\s+$//;   #trim trailing whitespace
      $ilnodelist = substr($oneline,42,32);
      $ilnodelist =~ s/\s+$//;   #trim trailing whitespace
      newlst($ilnode,$ilnodelist);
   }


   # (4) the TNAME data
   open(KTNA, "< $opt_txt_tname") || die("Could not open tdname $opt_txt_tname\n");
   @ktna_data = <KTNA>;
   close(KTNA);

   $ll = 0;
   foreach $oneline (@ktna_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $iid = substr($oneline,0,32);
      $iid =~ s/\s+$//;   #trim trailing whitespace
      $ifullname = substr($oneline,33,256);
      $ifullname =~ s/\s+$//;   #trim trailing whitespace
      next if $ifullname eq "";
      $sitfullx{$iid} = $ifullname;
   }

   # (5) the TSITDESC data
   open(KSIT, "< $opt_txt_tsitdesc") || die("Could not open sit $opt_txt_tsitdesc\n");
   @ksit_data = <KSIT>;
   close(KSIT);

   $ll = 0;
   foreach $oneline (@ksit_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $oneline .= " " x 1000;
      $isitname = substr($oneline,0,32);
      $isitname =~ s/\s+$//;   #trim trailing whitespace
      $iautostart = substr($oneline,33,4);
      $iautostart =~ s/\s+$//;   #trim trailing whitespace
      next if substr($isitname,0,8) eq "UADVISOR";
      next if $iautostart eq "*SYN";
      if ($iautostart eq "*NO") {
         next if $opt_runall == 0;
      }
      $isitinfo = substr($oneline,38,128);
      $isitinfo =~ s/\s+$//;   #trim trailing whitespace
      $icmd = substr($oneline,167,5);
      $icmd =~ s/\s+$//;   #trim trailing whitespace
      $ireev_days = substr($oneline,674,3);
      $ireev_days =~ s/\s+$//;   #trim trailing whitespace
      $ireev_time = substr($oneline,680,6);
      $ireev_time =~ s/\s+$//;   #trim trailing whitespace
      $ipdt = "";
      if (length($oneline) > 695) {
         $ipdt = substr($oneline,689,1020);
         $ipdt =~ s/\s+$//;   #trim trailing whitespace
      }
      $itext = "";
      if (length($oneline) > 1715) {                     #???
         $itext = substr($oneline,1714,64);
         $itext =~ s/\s+$//;   #trim trailing whitespace
      }
      newsit($isitname,$ipdt,"",$iautostart,$isitinfo,$ireev_days,$ireev_time);
      $sit_text[$siti] = $itext;
      $sit_fullname[$siti] = $sitfullx{$isitname} if defined $sitfullx{$isitname};
   }

   # (6) the TNODESAV data
   open(KNOD, "< $opt_txt_tnodesav") || die("Could not open tnodesav $opt_txt_tnodesav\n");
   @knod_data = <KNOD>;
   close(KNOD);

   $ll = 0;
   foreach $oneline (@knod_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $oneline .= " " x 400;
      $iagt = substr($oneline,0,32);
      $iagt =~ s/\s+$//;   #trim trailing whitespace
      $ihostinfo = substr($oneline,33,16);
      $ihostinfo =~ s/\s+$//;   #trim trailing whitespace
      $iversion = substr($oneline,50,8);
      $iversion =~ s/\s+$//;   #trim trailing whitespace
      $ihostaddr = substr($oneline,51,256);
      $ihostaddr =~ s/\s+$//;   #trim trailing whitespace
      newagt($iagt,$ihostinfo,$iversion,$ihostaddr);
   }


   open(KCALE, "< $opt_txt_tcalendar") || die("Could not open TCALENDAR $opt_txt_tcalendar\n");
   @kcale_data = <KCALE>;
   close(KCALE);
   # Get data for all TCALENDAR records
   $ll = 0;
   foreach $oneline (@kcale_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $oneline .= " " x 400;
      $iname = substr($oneline,00,256);
      $iname =~ s/\s+$//;   #trim trailing whitespace
      $calex{$iname} = 1;
   }

   open(KOVRD, "< $opt_txt_toverride") || die("Could not open TOVERRIDE $opt_txt_toverride\n");
   @kovrd_data = <KOVRD>;
   close(KOVRD);
   # Get data for all TOVERRIDE records
   $ll = 0;
   foreach $oneline (@kovrd_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $oneline .= " " x 400;
      $iname = substr($oneline,00,256);
      $iname =~ s/\s+$//;   #trim trailing whitespace
      $overx{$iname} = 1;
   }

   open(KPCYF, "< $opt_txt_tpcydesc") || die("Could not open TPCYDESC $opt_txt_tpcydesc\n");
   @kpcyf_data = <KPCYF>;
   close(KPCYF);

   # Get data for all TPCYDESC records
   $ll = 0;
   foreach $oneline (@kpcyf_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $oneline .= " " x 400;
      $iname = substr($oneline,0,32);
      $iname =~ s/\s+$//;   #trim trailing whitespace
      $pcyfx{$iname} = 1;
   }

   # (7) the TOBJACCL data - basically distributions
   open(KOBJ, "< $opt_txt_tobjaccl") || die("Could not open tobjaccl $opt_txt_tobjaccl\n");
   @kobj_data = <KOBJ>;
   close(KOBJ);

   $ll = 0;
   foreach $oneline (@kobj_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $iobjname = substr($oneline,0,32);
      $iobjname =~ s/\s+$//;   #trim trailing whitespace
      $iobjclass = substr($oneline,33,4);
      $iobjclass =~ s/\s+$//;   #trim trailing whitespace
      $inodel = substr($oneline,42,32);
      $inodel =~ s/\s+$//;   #trim trailing whitespace


      # Situation type distribution
      if ($iobjclass eq '5140') {
         $sx = $sitx{$iobjname};
         next if !defined $sx;
         my $nx = $lnodlx{$inodel};        # is the NODEL a known MSL
         if ($sit_autostart[$sx] eq "*NO") {
            $lnodl_off_ct[$nx] += 1 if defined $nx;    # non-autostarted situations with this MSL
         } else {
            if (defined $nx) {                # yes
               $lnodl_sit_ct[$nx] += 1;
               push @{$sit_agents[$sx]},@{$lnodl_nodes[$nx]};
               foreach $n (@{$lnodl_nodes[$nx]}) {
                   my @aref = ["M",$inodel];
                   push @{$sit_agenth[$sx]{$n}}, \@aref;
               }
            } elsif (defined $agtx{$inodel}) {                    # not, likely an agent name
               my @aref = ["A",$inodel];
               push @{$sit_agenth[$sx]{$inodel}}, \@aref;
            }
            $sit_dist[$sx] = 1;
            $sit_distribution = 1;
         }

      # Situation Group type distribution
      } elsif ($iobjclass eq '2010')   {
          $gx = $grpx{$iobjname};
          next if !defined $gx;
          %sum_sits = ();
          sitgroup_get_sits($gx);
          foreach my $s (keys %sum_sits) {
             $sx =  $sitx{$s};
             next if !defined $sx;
             my $nx = $lnodlx{$inodel};        # is the NODEL a known MSL
             if (defined $nx) {                # yes
                $lnodl_sit_ct[$nx] += 1;
                push @{$sit_agents[$sx]},@{$lnodl_nodes[$nx]};
                foreach $n (@{$lnodl_nodes[$nx]}) {
                   my @aref = ["GM",$inodel,$grp_name[$gx]];
                   push @{$sit_agenth[$sx]{$n}}, \@aref;
               }
             } elsif (defined $agtx{$inodel}) {                    # not, likely an agent name
                my @aref = ["GA",$inodel,$grp_name[$gx]];
                push @{$sit_agenth[$sx]{$inodel}}, \@aref;
             }
             $sit_dist[$sx] = 1;
             $sit_distribution = 1;
          }
      } elsif ($iobjclass eq '5652')   {    # Calendar distribution
         my $nx = $lnodlx{$inodel};        # is the NODEL a known MSL
         if (defined $nx) {                # yes
            $lnodl_cal_ct[$nx] += 1 if defined $calex{$iobjname};
         }
      } elsif ($iobjclass eq '5130')   {    # Policy distribution
         my $nx = $lnodlx{$inodel};        # is the NODEL a known MSL
         if (defined $nx) {                # yes
            $lnodl_ovr_ct[$nx] += 1 if defined $overx{$iobjname};
         }
      } elsif ($iobjclass eq '5650')   {    # Override distribution
         my $nx = $lnodlx{$inodel};        # is the NODEL a known MSL
         if (defined $nx) {                # yes
            $lnodl_pcy_ct[$nx] += 1 if defined $pcyfx{$iobjname};
         }
      }
   }

}

# There may be a better way to do this, but this was clear and worked.
# The input $lcount must be matched up to the number of columns
# SELECTED in the SQL.
# [1]  OGRP_59B815CE8A3F4403  OGRP_6F783DF5FF904988  2010  2010
sub parse_lst {
  my ($lcount,$inline) = @_;            # count of desired chunks and the input line
  my @retlist = ();                     # an array of strings to return
  my $chunk = "";                       # One chunk
  my $oct = 1;                          # output chunk count
  my $rest;                             # the rest of the line to process
  $inline =~ /\]\s*(.*)/;               # skip by [NNN]  field
  $rest = " " . $1 . "        ";
  my $lenrest = length($rest);          # length of $rest string
  my $restpos = 0;                      # postion studied in the $rest string
  my $nextpos = 0;                      # floating next position in $rest string

  # at each stage we can identify a field with values
  #         <blank>data<blank>
  # and a blank field
  #         <blank><blank>
  # We allow a single embedded blank as part of the field
  #         data<blank>data
  # for the last field, we allow imbedded blanks and logic not needed
  while ($restpos < $lenrest) {
     if ($oct < $lcount) {
        if (substr($rest,$restpos,2) eq "  ") {               # null string case
           $chunk = "";
           $oct += 1;
           push @retlist, $chunk;                 # record null data chunk
           $restpos += 2;
        } else {
           $nextpos = index($rest," ",$restpos+1);
           if (substr($rest,$nextpos,2) eq "  ") {
              $chunk .= substr($rest,$restpos+1,$nextpos-$restpos-1);
              push @retlist, $chunk;                 # record null data chunk
              $chunk = "";
              $oct += 1;
              $restpos = $nextpos + 1;
           } else {
              $chunk .= substr($rest,$restpos+1,$nextpos-$restpos);
              $restpos = $nextpos;
           }
        }
     } else {
        $chunk = substr($rest,$restpos+1);
        $chunk =~ s/\s+$//;                    # strip trailing blanks
        push @retlist, $chunk;                 # record last data chunk
        last;
     }
  }
  return @retlist;
}

sub init_lst {
   my @kgrp_data;                 # TGROUP data    together form the Situation Group definitins
   my @kgrpi_data;                # TGROUPI data
   my @ksit_data;                 # TSITDESC - Situation Description
   my @ktna_data;                 # TNAME - NAME table for long situation names
   my @kobj_data;                 # TOBJACCL - Object Access List for distributions
   my @knod_data;                 # TNODESAV - disk copy of node status
   my @klst_data;                 # TNODELST - Type M - MSL definitions used
   my $isitname;
   my $ifullname;
   my $ipdt;
   my $iautostart;
   my $isitinfo;
   my $icmd;
   my $itext;
   my $ireev_days;
   my $ireev_time;
   my $iid;
   my $igrpclass;
   my $igrpname;
   my $iobjname;
   my $iobjclass;
   my $inodel;

   my $iagt;
   my $ihostinfo;
   my $iversion;
   my $ihostaddr;

   my $ilnodetype;
   my $ilnode;
   my $ilnodelist;

   # Parsing the KfwSQLClient output has some challenges. For example
   #      [1]  OGRP_59B815CE8A3F4403  2010  Test Group 1
   # Using the blank delimiter is OK for columns that are never blank or have no embedded blanks.
   # In this case the GRPNAME column is "Test Group 1". To manage this the SQL is arranged so
   # that a column with embedded blanks always placed at the end. The one table TSITDESC which has
   # two such columns is retrieved with two separate SQLs.
   #
   # The one case where a column might be blank is the TNODESAV HOSTINFO column. In that case
   # a fixup is performed in case the third column [VERSION] is blank,
   #
   # There may be similar fixes in the future.


   # (1) the TGROUP data  - get a list of IDs and prepare slots of SITs and GRPs
   open(KGRP, "< $opt_lst_tgroup") || die("Could not open TGROUP $opt_lst_tgroup\n");
   @kgrp_data = <KGRP>;
   close(KGRP);

   # make an array of all group identifications
   # [1]  OGRP_59B815CE8A3F4403  2010  Test Group 1
   $ll = 0;
   foreach $oneline (@kgrp_data) {
      $ll += 1;
      next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
      chop $oneline;
      next if substr($oneline,0,1) ne "[";
      print STDERR "working on KGRP line $ll\n" if $opt_v == 1;
      ($iid,$igrpclass,$igrpname) = parse_lst(3,$oneline);
      next if $igrpclass ne '2010';
      $igrpname =~ s/\s+$//;   #trim trailing whitespace
      $gx = $grpx{$iid};
      if (!defined $gx) {
         $grpi++;
         $gx = $grpi;
         $grp[$gx] = $iid;
         $grpx{$iid} = $gx;
         $grp_name[$gx] = $igrpname;
         $grp_sit[$gx] = {};
         $grp_grp[$gx] = {};
      }
   }

   # (2) the TGROUPI data
   open(KGRPI, "< $opt_lst_tgroupi") || die("Could not open TGROUPI $opt_lst_tgroupi !@\n");
   @kgrpi_data = <KGRPI>;
   close(KGRPI);

   # digest the TGROUP items
   # [1]  OGRP_59B815CE8A3F4403  OGRP_6F783DF5FF904988  2010  2010
   # Work through all the group items
   $ll = 0;
   foreach $oneline (@kgrpi_data) {
      $ll += 1;
      next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
      chop $oneline;
      next if substr($oneline,0,1) ne "[";
      print STDERR "working on KGRPI line $ll\n" if $opt_v == 1;
      ($iid,$iobjname,$iobjclass,$igrpclass) = parse_lst(4,$oneline);
      next if $igrpclass ne '2010';
      if (($iobjclass ne '5140') & ($iobjclass ne '2010')) {
         next;
      }
      $gx = $grpx{$iid};
      if (!defined $gx) {
         warn "unknown group id $iid.\n";
         next;
      }
      $grp_sit[$gx]->{$iobjname} = 1 if $iobjclass eq '5140';
      $grp_grp[$gx]->{$iobjname} = 1 if $iobjclass eq '2010';
   }
   # digest the  the TNODELST data - M type which agent/nodelist data
   # [1]  M  nmp180:SY  *AGGREGATION_AND_PRUNING
   open(KLST, "< $opt_lst_tnodelst") || die("Could not open tnodelst $opt_lst_tnodelst\n");
   @klst_data = <KLST>;
   close(KLST);

   $ll = 0;
   foreach $oneline (@klst_data) {
      $ll += 1;
      next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
      chop $oneline;
      next if substr($oneline,0,1) ne "[";
      print STDERR "working on KLST line $ll\n" if $opt_v == 1;
      ($ilnodetype,$ilnode,$ilnodelist) = parse_lst(3,$oneline);
      if (!defined $ilnodelist) {
         $ilnodelist = $ilnode;
         $ilnode = $ilnodetype;
         $ilnodetype = "M";
      }
      next if $ilnodetype ne "M";
      $ilnode =~ s/\s+$//;   #trim trailing whitespace
      $ilnodelist =~ s/\s+$//;   #trim trailing whitespace
      newlst($ilnode,$ilnodelist);
   }


   # (4) the TNAME data
   # [1]  ZIBM_STATIC134_24CA0B4D91DB4FFD  IBM-test-length
   my $go_tname = 1;
   open(KTNA, "< $opt_lst_tname") or $go_tname = 0;
   warn("Could not open tname $opt_lst_tname\n") if $go_tname == 0;
   if ($go_tname == 1) {
      @ktna_data = <KTNA>;
      close(KTNA);

      $ll = 0;
      foreach $oneline (@ktna_data) {
         $ll += 1;
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
         chop $oneline;
         next if substr($oneline,0,1) ne "[";
         print STDERR "working on KTNA line $ll\n" if $opt_v == 1;
         ($iid,$ifullname) = parse_lst(2,$oneline);
         $iid =~ s/\s+$//;   #trim trailing whitespace
         $ifullname =~ s/\s+$//;   #trim trailing whitespace
         next if $ifullname eq "";
         $sitfullx{$iid} = $ifullname;
      }
   }

   # (5) the TSITDESC data
   # [1]  Deploy_Failed  *NO  ATOM=KDYDYST.TARGETMSN;SEV=Critical;TFWD=Y;OV=N;~  *NONE  NNN  0  000200  *IF *VALUE Deploy_status.Status *EQ Failed
   open(KSIT, "< $opt_lst_tsitdesc") || die("Could not open sit $opt_lst_tsitdesc\n");
   @ksit_data = <KSIT>;
   close(KSIT);

   $ll = 0;
   foreach $oneline (@ksit_data) {
      $ll += 1;
      next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
      chop $oneline;
      next if substr($oneline,0,1) ne "[";
      print STDERR "working on KSIT line $ll\n" if $opt_v == 1;
      ($isitname,$iautostart,$isitinfo,$ireev_days,$ireev_time,$ipdt) = parse_lst(6,$oneline);
      $isitname =~ s/\s+$//;   #trim trailing whitespace
      $iautostart =~ s/\s+$//;   #trim trailing whitespace
      next if substr($isitname,0,8) eq "UADVISOR";  # ignore UADVISOR tables
      next if $iautostart eq "*SYN";                # ignore *SYN utility situations
      if ($iautostart eq "*NO") {                   # ignore autostart=*NO unless -runall is specified
         next if $opt_runall == 0;
      }
      $isitinfo =~ s/\s+$//;   #trim trailing whitespace
      $ireev_days =~ s/\s+$//;   #trim trailing whitespace
      $ireev_time =~ s/\s+$//;   #trim trailing whitespace
      newsit($isitname,$ipdt,"",$iautostart,$isitinfo,$ireev_days,$ireev_time);
      $sit_fullname[$siti] = $sitfullx{$isitname} if defined $sitfullx{$isitname};
   }

   # (5A) the TSITDESC data - TEXTs columns
   # [1]  IBM_Offline_action  echo   &{ManagedSystem.Name}  offline at  &{ManagedSystem.Timestamp} >>/tmp/offline.log
   open(KSIT, "< $opt_lst_tsitdesc2") || die("Could not open sit $opt_lst_tsitdesc2\n");
   @ksit_data = <KSIT>;
   close(KSIT);

   $ll = 0;
   foreach $oneline (@ksit_data) {
      $ll += 1;
      next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
      chop $oneline;
      next if substr($oneline,0,1) ne "[";
      print STDERR "working on KSIT2 line $ll\n" if $opt_v == 1;
      ($isitname,$itext) = parse_lst(2,$oneline);
      $isitname =~ s/\s+$//;   #trim trailing whitespace
      $sx = $sitx{$isitname};
      $itext =~ s/\s+$//;   #trim trailing whitespace
      $sit_text[$sx] = $itext if defined $sx;
   }

   # (6) the TNODESAV data
   # [1]  HUB_NMP180    06.30.03
   open(KNOD, "< $opt_lst_tnodesav") || die("Could not open tnodesav $opt_lst_tnodesav\n");
   @knod_data = <KNOD>;
   close(KNOD);

   $ll = 0;
   foreach $oneline (@knod_data) {
      $ll += 1;
      next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
      chop $oneline;
      next if substr($oneline,0,1) ne "[";
      print STDERR "working on KNOD line $ll\n" if $opt_v == 1;
      ($iagt,$ihostinfo,$iversion,$ihostaddr) = parse_lst(4,$oneline);
      if ($iversion eq "") {
         $iversion = $ihostinfo;
         $ihostinfo = "";
      }
      $iagt =~ s/\s+$//;   #trim trailing whitespace
      $ihostinfo =~ s/\s+$//;   #trim trailing whitespace
      $iversion =~ s/\s+$//;   #trim trailing whitespace
      newagt($iagt,$ihostinfo,$iversion,$ihostaddr);
   }


   # (7) the TOBJACCL data - basically distributions
   # [1]  Deploy_Failed  5140  *HUB
   open(KOBJ, "< $opt_lst_tobjaccl") || die("Could not open tobjaccl $opt_lst_tobjaccl\n");
   @kobj_data = <KOBJ>;
   close(KOBJ);

   # Distribution can be for multiple overlapping reasons
   #   1) by Agent
   #   2) by MSL
   #   3) Situation group by agent
   #   4) Situation group by MSL
   # and any one of these could be duplicated or absent.
   # Thus the @sit_agenth - or agent reason hash contains an hash of arrays of arrays.
   #   The hash key is the managed system name or agent name
   #    the first level array is the list of reasons why situation is distributed.
   #       the second level array is each reason with 2 or 3 elements
   #            A,Agent
   #            M,MSL
   #            GA,A,Groupname
   #            GM,MSL,Groupname
   #
   #  this result is captured in the sitinfo.json output along with situation name etc.

   $ll = 0;
   foreach $oneline (@kobj_data) {
      $ll += 1;
      next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
      chop $oneline;
      next if substr($oneline,0,1) ne "[";
      print STDERR "working on KOBJ line $ll\n" if $opt_v == 1;
      ($iobjname,$iobjclass,$inodel) = parse_lst(3,$oneline);
      $iobjname =~ s/\s+$//;   #trim trailing whitespace
      $iobjclass =~ s/\s+$//;   #trim trailing whitespace
      $inodel =~ s/\s+$//;   #trim trailing whitespace

      # Situation type distribution
      if ($iobjclass eq '5140') {
         $sx = $sitx{$iobjname};
         next if !defined $sx;
         my $nx = $lnodlx{$inodel};        # is the NODEL a known MSL
         if (defined $nx) {                # yes
            $lnodl_sit_ct[$nx] += 1;
            push @{$sit_agents[$sx]},@{$lnodl_nodes[$nx]};
            foreach $n (@{$lnodl_nodes[$nx]}) {
                my @aref = ["M",$inodel];
                push @{$sit_agenth[$sx]{$n}}, \@aref;
            }
         } elsif (defined $agtx{$inodel}) {                    # not, likely an agent name
            my @aref = ["A",$inodel];
            push @{$sit_agenth[$sx]{$inodel}}, \@aref;
         }
         $sit_dist[$sx] = 1;
         $sit_distribution = 1;

      # Situation Group type distribution
      } elsif ($iobjclass eq '2010')   {
          $gx = $grpx{$iobjname};
          next if !defined $gx;
          %sum_sits = ();
          sitgroup_get_sits($gx);
          foreach my $s (keys %sum_sits) {
             $sx =  $sitx{$s};
             next if !defined $sx;
             my $nx = $lnodlx{$inodel};        # is the NODEL a known MSL
             if (defined $nx) {                # yes
                $lnodl_sit_ct[$nx] += 1;
                push @{$sit_agents[$sx]},@{$lnodl_nodes[$nx]};
                foreach $n (@{$lnodl_nodes[$nx]}) {
                   my @aref = ["GM",$inodel,$grp_name[$gx]];
                   push @{$sit_agenth[$sx]{$n}}, \@aref;
               }
             } elsif (defined $agtx{$inodel}) {                    # not, likely an agent name
                my @aref = ["GA",$inodel,$grp_name[$gx]];
                push @{$sit_agenth[$sx]{$n}}, \@aref;
             }
             $sit_dist[$sx] = 1;
             $sit_distribution = 1;
          }
      }
   }
}


# Get options from command line - first priority
sub init {
   my $myargs_remain;
   my @myargs_remain_array;
   use Getopt::Long qw(GetOptionsFromString);
   $myargs = shift;

   ($rc,$myargs_remain) = GetOptionsFromString($myargs,
              'log=s' => \ $opt_log,                  # log file
              'ini=s' => \ $opt_ini,                  # control file
              'debuglevel=i' => \ $opt_debuglevel,    # log file contents control
              'debug' => \ $opt_debug,                # log file contents control
              'h' => \ $opt_h,                        # help
              'v' => \  $opt_v,                       # verbose - print immediately as well as log
              'vt' => \  $opt_vt,                     # verbose traffic - print traffic.txt
              'o=s' => \ $opt_o,                      # output file
              'workpath=s' => \ $opt_workpath,        # output file
              'runall' => \$opt_runall,               # analyze Run at Startup = *Off situations
              'std' => \ $opt_std,                    # credentials from standard input
              'zero' => \ $opt_zero,                  # Show situations Run on startup but zero distribution
              'onerow' => \ $opt_onerow,              # Show situations Run on startup but zero distribution
              'txt' => \ $opt_txt,                    # txt input
              'lst' => \ $opt_lst,                    # txt input
              'remove' => \ $opt_remove               # want remove.cmd and remove.sh files
             );
   # if other things found on the command line - complain and quit
   @myargs_remain_array = @$myargs_remain;
   if ($#myargs_remain_array != -1) {
      foreach (@myargs_remain_array) {
        print STDERR "SITINFO001E Unrecognized command line option - $_\n";
      }
      print STDERR "SITINFO001E exiting after command line errors\n";
      exit 1;
   }

   # Following are command line only defaults. All others can be set from the ini file

   if (!defined $opt_ini) {$opt_ini = "sitinfo.ini";}         # default control file if not specified
   if ($opt_h) {&GiveHelp;}  # GiveHelp and exit program
   if (!defined $opt_debuglevel) {$opt_debuglevel=90;}         # debug logging level - low number means fewer messages
   if (!defined $opt_debug) {$opt_debug=0;}                    # debug - turn on rare error cases
   if (defined $opt_txt) {
      $opt_txt_tsitdesc = "QA1CSITF.DB.TXT";
      $opt_txt_tname =    "QA1DNAME.DB.TXT";
      $opt_txt_tobjaccl = "QA1DOBJA.DB.TXT";
      $opt_txt_tgroup   = "QA1DGRPA.DB.TXT";
      $opt_txt_tgroupi  = "QA1DGRPI.DB.TXT";
      $opt_txt_tnodesav  = "QA1DNSAV.DB.TXT";
      $opt_txt_tnodelst  = "QA1CNODL.DB.TXT";
      $opt_txt_tcalendar = "QA1DCALE.DB.TXT";
      $opt_txt_toverride = "QA1DOVRD.DB.TXT";
      $opt_txt_tpcydesc = "QA1DPCYF.DB.TXT";
   }
   if (defined $opt_lst) {
      $opt_lst_tsitdesc = "QA1CSITF.DB.LST";
      $opt_lst_tsitdesc1 = "QA1CSITF1.DB.LST";
      $opt_lst_tsitdesc2 = "QA1CSITF2.DB.LST";
      $opt_lst_tname =    "QA1DNAME.DB.LST";
      $opt_lst_tobjaccl = "QA1DOBJA.DB.LST";
      $opt_lst_tgroup   = "QA1DGRPA.DB.LST";
      $opt_lst_tgroupi  = "QA1DGRPI.DB.LST";
      $opt_lst_tnodesav  = "QA1DNSAV.DB.LST";
      $opt_lst_tnodelst  = "QA1CNODL.DB.LST";
      $opt_lst_tcalendar = "QA1DCALE.DB.LST";
      $opt_lst_toverride = "QA1DOVRD.DB.LST";
      $opt_lst_tpcydesc = "QA1DPCYF.DB.LST";
   }

   # ini control file must be present

   if (-e $opt_ini) {                                      # make sure ini file is present

      open( FILE, "< $opt_ini" ) or die "Cannot open ini file $opt_ini : $!";
      my @ips = <FILE>;
      close FILE;

      # typical ini file scraping. Could be improved by validating parameters

      my $l = 0;
      foreach my $oneline (@ips)
      {
         $l++;
         chomp($oneline);
         next if (substr($oneline,0,1) eq "#");  # skip comment line
         @words = split(" ",$oneline);
         next if $#words == -1;                  # skip blank line
          if ($#words == 0) {                         # single word parameters
            if ($words[0] eq "verbose") {$opt_v = 1;}
            elsif ($words[0] eq "traffic") {$opt_vt = 1;}
            elsif ($words[0] eq "std") {$opt_std = 1;}
            elsif ($words[0] eq "runall") {$opt_runall = 1;}            # all agents of interest
            elsif ($words[0] eq "onerow") {$opt_onerow = 1;}            # onerow style
            else {
               print STDERR "SITINFO003E Control without needed parameters $words[0] - $opt_ini [$l]\n";
               $run_status++;
            }
            next;
         }

         if ($#words == 1) {
            # two word controls - option and value
            if ($words[0] eq "log") {$opt_log = $words[1];}
            elsif ($words[0] eq "log") {$opt_log = $words[1];}
            elsif ($words[0] eq "o") {$opt_o = $words[1];}
            elsif ($words[0] eq "workpath") {$opt_workpath = $words[1];}
            else {
               print STDERR "SITINFO005E ini file $l - unknown control oneline\n"; # kill process after current phase
               $run_status++;
            }
            next;
         }
         if ($#words == 3) {
            # four+ word controls - option and three values and optional message template
            if ($words[0] eq "txt") {
               $opt_txt=1;
               $opt_txt_tsitdesc=$words[1];
               $opt_txt_tname=$words[2];
               $opt_txt_tobjaccl=$words[3];
            } else {
               print STDERR "SITINFO005E ini file $l - unknown control $oneline\n"; # kill process after current phase
               $run_status++;
            }
            next;
         }
         print STDERR "SITINFO005E ini file $l - unknown control $oneline\n"; # kill process after current phase
         $run_status++;
      }
   }

   # defaults for options not set otherwise

   if (!defined $opt_log) {$opt_log = "sitinfo.log";}           # default log file if not specified
   if (!defined $opt_h) {$opt_h=0;}                            # help flag
   if (!defined $opt_v) {$opt_v=0;}                            # verbose flag
   if (!defined $opt_vt) {$opt_vt=0;}                          # verbose traffic default off
   if (!defined $opt_dpr) {$opt_dpr=0;}                        # data dump flag
   if (!defined $opt_std) {$opt_std=0;}                        # default - no credentials in stdin
   if (!defined $opt_o) {$opt_o="sitinfo.csv";}               # default output file
   if (!defined $opt_workpath) {$opt_workpath="";}             # default is current directory
   if (!defined $opt_runall) {$opt_runall = 0;}                # default no Run at Startup = *YES situations
   if (!defined $opt_txt) {$opt_txt = 0;}                      # default no txt input
   if (!defined $opt_lst) {$opt_lst = 0;}                      # default no lst input

   $opt_workpath =~ s/\\/\//g;                                 # convert to standard perl forward slashes
   if ($opt_workpath ne "") {
      $opt_workpath .= "\/" if substr($opt_workpath,length($opt_workpath)-1,1) ne "\/";
   }


   if ($opt_dpr == 1) {
#     my $module = "Data::Dumper";
#     eval {load $module};
#     if ($@) {
#        print STDERR "Cannot load Data::Dumper - ignoring -dpr option\n";
#        $opt_dpr = 0;
#     }
      $opt_dpr = 0;
   }

   # if credential as passed in via standard input, then that takes precendence.

   # complain about options which must be present
   if (($opt_txt + $opt_lst) != 1) {
      print STDERR "SITINFO006E exactly one of txt/lst must be present\n";
      $run_status++;
   }

   # if any errors, then dump log and exit
   # this way we can show multiple errors at startup
   if ($run_status) { exit 1;}

}



#------------------------------------------------------------------------------
sub GiveHelp
{
  $0 =~ s|(.*)/([^/]*)|$2|;
  print <<"EndOFHelp";

  $0 v$gVersion

  This script surveys an ITM environment reporting in situation distributions

  Default values:
    log           : sitinfo.log
    ini           : sitinfo.ini
    debuglevel    : 90 [considerable number of messages]
    debug         : 0  when 1 some breakpoints are enabled]
    h             : 0  display help information
    v             : 0  display log messages on console
    vt            : 0  record http traffic on traffic.txt file
    dpr           : 0  dump data structure if Dump::Data installed
    lst           :    get data from KfwSQLClient SQL data
    txt           :    get data from TEMS2SQL data

  Example invovation
    $0  -lst

  Note: $0 uses an initialization file [default sitinfo.ini] for some controls.

EndOFHelp
exit;
}


#------------------------------------------------------------------------------
# capture log record
sub logit
{
   my $level = shift;
   if ($level <= $opt_debuglevel) {
      my $iline = shift;
      my $itime = gettime();
      chop($itime);
      my $oline = $itime . " " . $level . " " . $iline;
      if ($opt_debuglevel >= 100) {
         my $ofile = (caller(0))[1];
         my $olino = (caller(0))[2];
         if (defined $ofile) {
            $oline = $ofile . ":" . $olino . " " . $oline;
         }
      }
      print FH "$oline\n";
      print "$oline\n" if $opt_v == 1;
   }
}

#------------------------------------------------------------------------------
# capture agent log record
#------------------------------------------------------------------------------
# capture agent error record

# write output log
sub datadumperlog
{
   require Data::Dumper;
   my $dd_msg = shift;
   my $dd_var = shift;
   print FH "$dd_msg\n";
   no strict;
   print FH Data::Dumper->Dumper($dd_var);
}

# return timestamp
sub gettime
{
   my $sec;
   my $min;
   my $hour;
   my $mday;
   my $mon;
   my $year;
   my $wday;
   my $yday;
   my $isdst;
   ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst)=localtime(time);
   return sprintf "%4d-%02d-%02d %02d:%02d:%02d\n",$year+1900,$mon+1,$mday,$hour,$min,$sec;
}

# get current time in ITM standard timestamp form
# History log

# 0.50000  : New script based on ITM Health Survey 1.11000
# 0.60000  : Remove soap option for the time being
# 0.61000  : Handle -lst parsing better and fix sitinfo.sh
# 0.62000  : Handle -lst parsing when sitinfo is blank
# 0.63000  : better -lst parsing
# 0.64000  : Add -onerow to get agent per row
# 0.66000  : Better parse_list logic
# 0.67000  : Better parse_list logic
# 0.68000  : Add unused MSL report section
# 0.69000  : improve unused MSL report section
# 0.70000  : In -onerow add column to option to claify why situation distributed
# 0.71000  : Correct unused MSL count and add list of used MSL and counts
# 0.73000  : Correct handling of Sitgroup distribution by agent name
# 0.74000  : Add knowledge of distribution for TCALENDAR, TOVERRIDE and POLICY
# 0.75000  : Remove json output to ease customer use - original logic in sitinfo_json.pl
# 0.76000  : Count situation impact on agents
# 0.77000  : Add Persist to onerow report
# 0.78000  : Add Text [Description] to onerow report
# 0.79000  : Correct Description capture for -lst option
# 0.80000  : Correct sitinfo.sh and sitinfo.cmd output file redirection
