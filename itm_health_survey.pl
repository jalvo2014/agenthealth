#!/usr/local/bin/perl -w
#------------------------------------------------------------------------------
# Licensed Materials - Property of IBM (C) Copyright IBM Corp. 2010, 2010
# All Rights Reserved US Government Users Restricted Rights - Use, duplication
# or disclosure restricted by GSA ADP Schedule Contract with IBM Corp
#------------------------------------------------------------------------------

#  perl itm_zombie_survey.pl
#
#  Identify agents that may be online but not responsive
#  Read the first record of the operations log in groups.
#
#  john alvord, IBM Corporation, 24 August 2013
#  jalvord@us.ibm.com
#
# tested on Windows Activestate 5.12.2
#
# $DB::single=2;   # remember debug breakpoint

use strict;
use warnings;

# short history at end of module

my $gVersion = "0.60000";
my $gWin = (-e "C://") ? 1 : 0;    # 1=Windows, 0=Linux/Unix

BEGIN {
   $ENV{'PERL_NET_HTTPS_SSL_SOCKET_CLASS'} = "Net::SSL";
   $ENV{'PERL_LWP_SSL_VERIFY_HOSTNAME'} = 0;
};   #

my $zombie_start = time;

#  use warnings::unused; # installs the check routine as 'once'
#  use warnings 'once';  # enables  the check routine


use DateTime;                   # Computing with Date Time
#use SOAP::Lite +trace => 'all';        # simple SOAP processing. add 'debug' to increase tracing
use SOAP::Lite;                 # simple SOAP processing. add 'debug' to increase tracing
use HTTP::Request::Common;      #   and HTTP - for SOAP processing
use XML::TreePP;                # parse XML
#use Module::Load;               # more flexible
#use Data::Dumper;               # debug only
#use LWP::UserAgent;
#use LWP::Debug;
#LWP::Debug::level('+');
#SOAP::Lite->import(+trace => 'all');

# following object used to parse SOAP results and xml files.
# Originally XML::Simple was used but it malfunctioned on one platform.
my $tpp = XML::TreePP->new;

# a collection of variables which are used throughout the program.
# defined globally

my $args_start = join(" ",@ARGV);      # capture arguments for later processing
my $soap_rc;                           # return code from DoSoap call
my $soap_faultstr;                     # fault string from SOAP results
my $soap_faultcode;                    # fault code - where the fault originates
my $run_status = 0;                    # A count of pending runtime errors - used to allow multiple error detection before stopping process
my $oHub;                              # SOAP::Lite object to define connection

# some common variables

my @list = ();                         # used to get result of good SOAP capture
my $rc;
my $node;
my $nodelist;
my $product;
my $f;
my $ptx;
my $s_errcode;
my $s_erritem;
my $s_errtext;
my $myargs;
my $survey_sqls = 0;                     # count of SQLs
my $survey_sql_time = 0;                 # record total elapsed time in SQL processing
my @words = ();
my $rt;
my $tlen;
my $tlen1;
my $key;
my $save_timeout;
my $debugfile;
my $ll;
my $pcount;

# forward declarations of subroutines

sub init;                                # read command line and ini file
sub logit;                               # queue one record to survey log
sub dumplog;                             # dump current log to disk file
sub dumplogexit;                         # dump current log to disk file and exit
sub survey_agent;                        # Survey one agent
sub tems_node_analysis;                   # perform analysis of TEMS node status
sub DoSoap;                              # perform a SOAP request and return results
sub get_timestamp;                       # get current timestatmp
sub calc_timestamp;                      # Add or subtract time from an ITM timestamp
sub get_ITM_epoch;                       # convert from ITM timestamp to epoch seconds
sub datadumperlog;                       # dump a variable using Dump::Data if installed
sub get_connection;                      # get current connection string

# runtime Statistics variables
my $survey_tems = 0;                     # count of times TEMS surveyed


# option and ini file variables variables

my $opt_log;                    # name of log file
my $opt_ini;                    # name of ini file
my $opt_debuglevel;             # Debug level
my $opt_debug;                  # Debug level
my $opt_h;                      # help file
my $opt_v;                      # verbose flag
my $opt_vt;                     # verbose traffic flag
my @opt_pc = ();                # Product codes - like ux for Unix OS Agent
my %opt_pcx = ();               # index to Product codes
my @opt_tems = ();              # TEMS names to survey
my %opt_temsx = ();             # index to TEMS names
my $opt_dpr;                    # dump data structure flag
my $opt_std;                    # Credentials from standard input
my $opt_agent_timeout;          # How long to wait for agents
my $opt_soap_timeout;           # How long to wait SOAP request
my $opt_noretry;                # when 1 do not retry problem agents
my $opt_retry_timeout;          # delay time during retry, default 15
my $opt_o;                      # output file

my $user="";
my $passwd="";

# Parse control file which contains  operational defaults -
#
my @connections = ();               # list of possible hub TEMS servers
my $connection="";                  # one particular connection


$rc = init($args_start);

if ($opt_vt == 1) {
   open $debugfile, '>traffic.txt' or die "can't open 'traffic.txt': $!";;
   $debugfile->autoflush(1);
}

logit(0,"SURVEY000I - ITM_Zombie_Survey $gVersion $args_start");

# Variables

############
# SOAP Calls
############

# Variables associated directly with SOAP calls and responses
# CPU and Memory
my $sSQL;
my @log;
my $survey_count = 0;

# variables for storing Situation Description information from the hub TEMS

my $sx;
my @sitnames     = ();
my %sitnamex     = ();
my @sitobjaccl   = ();
my @situadaccl   = ();

my %objcobj = ();

# variables for storing node and nodelist information from the hub TEMS

my $snx;
my $nodli = -1;
my @snodlnames = ();
my %snodlx = ();
my @snodlnodes = ();

my $snodei = -1;                               # count of nodes
my @snode = ();                                # node names - managed system names
my %snodex = ();                               # index to nodenames
my %snode_filex = ();                          # index from *.review file to index
my @snode_survey_online = ();                  # used to track offline conditions
my @snode_survey_sits = ();                    # situations gotten from the survey - Run at Startup
my @snode_persist_sits = ();                   # persist ituations gotten from the survey
my @snode_survey_sits_noauto = ();             # situations gotten from the survey - not Run at Startup
my @snode_tems_product = ();                   # Product Code [Agent type] the agent is associated with
my @snode_tems_thrunode = ();                  # thrunode [remote TEMS for simple situations] the agent connects to
my @snode_tems_version = ();                   # version of [remote TEMS for simple situations] the agent connects to
my @snode_tems_hostaddr = ();                  # hostaddr information, include ip address
my @snode_agent_version = ();                  # version  information, include ip address
my @snode_agent_common  = ();                  # common software levels
my @snode_survey_maxdelay = ();                # maximum time to last situation started
my @snode_survey_maxdelay_situation = ();      # situation started
my @snode_survey_connects = ();                # count of connects
my @snode_survey_sitct = ();                   # count of situations running at the node
my @snode_survey_actions = ();                 # count of situation start/stop actions at the node
my @snode_agent_responsive = ();               # when 1, node was responsive
my @snode_agent_interested = ();               # when 1, node is being checked
my @snode_agent_retry      = ();               # when 1, retry needed
my @snode_agent_oplog1     = ();               # when non-null, invalid first oplog record

my $xprodi = -1;
my @xprod = ();
my %xprodx = ();
my %xprodn = ();
my @xprod_agent = ();
my @xprod_msl = ();

my $pxprodi = -1;
my @pxprod = ();
my %pxprodx = ();
my @pxprod_count = ();

my $tx;                                        # index
my $temsi = -1;                                # count of TEMSes in survey
my @tems = ();                                 # TEMS names
my %temsx = ();                                # index to TEMS
my @tems_time = ();                            # Current UTC time at the TEMS
my @tems_time_epoch = ();                      # Current UTC time at the TEMS in epoch seconds
my @tems_time_capture = ();                    # Epoch seconds at time capture
my @tems_thrunode = ();                        # thrunode - can be used to identify hub
my @tems_version = ();                         # version
my @tems_vmsize = ();                          # current process size
my @tems_cpubusy = ();                         # current process cpubusy
my @tems_server_busy = ();                     # current server cpubusy
my @tems_hostaddr = ();                        # current server host address
my $temsat = "";                               # AT clause for SQL to all TEMSes
my $tems_hub_nodeid = "";                      # nodeid of hub;


# variables for getting product information from the node status table

my $prodi = -1;
my @prodnames = ();
my %prodx = ();
my @prodsits = ();



# try out each SOAP connection, looking for the current FTO hub TEMS primary
# might be just one of course...

my $got_connection = 0;

foreach my $c (@connections) {
   #  Convert $connection as supplied by ini file into a connection string usable for soap processing
   #  That might be the string as supplied but might require changes to adapt to ports actually used
   $connection = $c;
   logit(0,"Survey trial of connection $connection");
   $rc = get_connection();
   if ($run_status) {
      logit(0,"Survey trial of connection $connection failed, continue to next");
      $DB::single=2 if $opt_debug == 1;
      $run_status = 0;
      next;
   }
#   $oHub = SOAP::Lite->proxy($connection,timeout => $opt_soap_timeout);
#   $oHub = SOAP::Lite->proxy($connection,keep_alive=>1,timeout => $opt_soap_timeout);
   $oHub = SOAP::Lite->proxy($connection,keep_alive=>1);
   $oHub->outputxml('true');
   $oHub->on_fault( sub {});      # pass back all errors


$oHub->transport->add_handler( request_send => sub {
#$DB::single=2;
    return if $opt_vt == 0;
    my $req = shift;
    my $cur_time = time;
    print $debugfile "\n$cur_time === BEGIN HTTP REQUEST ===\n";
    print $debugfile $req->dump(maxlength=>0);
    print $debugfile "\n$cur_time ===   END HTTP REQUEST ===\n";
    return
  }
);
$oHub->transport->add_handler( response_header => sub {
#$DB::single=2;
    return if $opt_vt == 0;
    my $cur_time = time;
    my $res = shift;
    print $debugfile "\n$cur_time === BEGIN RESPONSE HDRS ===\n";
    print $debugfile $res->dump(maxlength=>0);
    print $debugfile "\n$cur_time === END RESPONSE HDRS ===\n";
    return
  }
);
$oHub->transport->add_handler( response_data => sub {
    my $res = shift;
    my $cur_time = time;
    if ($opt_vt == 1) {
       my $content_length = length($res->content);
       print $debugfile "\n$cur_time === BEGIN HTTP RESPONSE DATA $content_length ===\n";
       print $debugfile $res->dump(maxlength=>0);
#      print $debugfile $res->content;
       print $debugfile "\n===   END HTTP RESPONSE DATA ===\n";
    }
#$DB::single=2;
#    if (substr($res->content,-20) eq "</SOAP-ENV:Envelope>") {
#       die "OK"; # Got whole data, not waiting for server to end the communication channel.
#    }
#    return 1; # In other cases make sure the handler is called for subsequent chunks
     return 1; # allow next chunk to come it...
}
);

$oHub->transport->add_handler( response_done => sub {
#$DB::single=2;
    my $res = shift;
    return if $opt_vt == 0;
    my $cur_time = time;
    print $debugfile "\n$cur_time === BEGIN HTTP RESPONSE DONE ===\n";
    print $debugfile $res->dump(maxlength=>0);
    print $debugfile "\n===   END HTTP RESPONSE DONE ===\n";
    return
  }
);

   # check to see if if TGBLBRKR table is available - present on ITM 622 and later
   logit(0,"Survey trial of connection $connection - check for TGBLBRKR presence");
   $sSQL = "SELECT TABL_NAME FROM SYSTEM.SYSTABLES WHERE TABL_NAME='TGBLBRKR'";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) {
      $DB::single=2 if $opt_debug == 1;
      logit(0,"Survey failure during check for TGBLBRKR presence");
      $run_status = 0;
      next;
   }
   if ($#list == -1) {
      $DB::single=2 if $opt_debug == 1;
      logit(0,"Survey TGBLBRKR is not present so cannot check for FTO hub TEMS primary role");
      last;
   }

   logit(0,"Survey trial of connection $connection - determine hub TEMS nodeid");
   $sSQL = "SELECT NODE, THRUNODE, HOSTADDR, VERSION FROM O4SRV.INODESTS WHERE O4ONLINE='Y' AND PRODUCT='EM' AND NODE=THRUNODE";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) {
      $DB::single=2 if $opt_debug == 1;
      $run_status = 0;
      next;
   }
   next if $#list == -1;
   $node = $list[0]-> {NODE};
   logit(0,"Survey trial of connection $connection TEMS $node - determine if hub TEMS is in primary role");
#  $sSQL = "SELECT ADDRESS, ANNOT, ENTRTYPE, PORT, PROTOCOL, ORIGINNODE FROM O4SRV.TGBLBRKR AT( '$node' ) WHERE ENTRTYPE = 1 AND ORIGINNODE = \'$node\'";
   $sSQL = "SELECT ADDRESS, ANNOT, ENTRTYPE, PORT, PROTOCOL, ORIGINNODE FROM O4SRV.TGBLBRKR WHERE ENTRTYPE = 1 AND ORIGINNODE = \'$node\'";
#  $save_timeout=$oHub->timeout;
#  $oHub->timeout(10);
   @list = DoSoap("CT_Get",$sSQL);
   $oHub->timeout($save_timeout);
   $save_timeout=$oHub->timeout(10);
   if ($run_status) {
      $DB::single=2 if $opt_debug == 1;
      $run_status = 0;
      next;
   }
   next if $#list == -1;
   logit(0,"Survey trial of connection $connection TEMS $node - has FTO primary role");
   $got_connection = 1;
   last;
}

if ($got_connection != 1) {
   logit(0,"Survey - no primary hub TEMS found - ending survey");
   dumplogexit;
}
dumplog;


# static analysis of the TEMS

logit(0,"Survey tems_node_analysis start");
$rc=tems_node_analysis();
logit(0,"Survey tems_node_analysis end");
dumplog;

my $in_id;
my $in_datetime;
my $in_node;

for (my $t=0; $t<=$temsi; $t++) {
   my $at_tems = $tems[$t];
   for (my $p=0; $p<=$xprodi; $p++) {
      my $at_product = $xprod[$p];
      my $at_nodelist = $xprod_msl[$p];
      logit(100,"working on $at_tems $at_product $at_nodelist");
      if ($at_nodelist eq ""){
         logit(10,"working on product[$at_product] null nodelist");
         next;
      }
      next if $at_nodelist eq "";
      $key = $at_tems . "_" . $at_product;
      logit(10,"working on $key nodelist[$at_nodelist] product_index[$p] tems[$at_tems] tems_index[$t]");
      $ptx = $pxprodx{$key};
      next if !defined  $ptx;
      next if $pxprod_count[$ptx] == 0;
      $tlen = length($nodelist);
      $tlen1 = length($opt_agent_timeout);
      $sSQL = "SELECT ID,DATETIME,ORIGINNODE FROM O4SRV.OPLOG AT('$at_tems') WHERE SYSTEM.PARMA('NODELIST','$at_nodelist',$tlen ) AND SYSTEM.PARMA('TIMEOUT','$opt_agent_timeout',$tlen1) AND ID='KRALOG000';";
      @list = DoSoap("CT_Get",$sSQL);

      # ignore errors
      if ($run_status == 0) {
         logit(0,"received $pcount responses for $at_nodelist at tems[$at_tems] product[$at_product]");
         if ($#list >= 0) {
            $pcount = $#list + 1;
            $ll = 0;
            foreach my $r (@list) {
               $ll++;
               my $count = scalar(keys %$r);
               if ($count < 3) {
                  logit(10,"working on OPLOG results row $ll of $pcount has $count instead of expected 3 keys");
                  next;
               }
               my $in_id = $r->{ID};
               $in_id =~ s/\s+$//;   #trim trailing whitespace
               $in_datetime = $r->{DATETIME};
               $in_datetime =~ s/\s+$//;   #trim trailing whitespace
               $in_node = $r->{System_Name};
               $in_node =~ s/\s+$//;   #trim trailing whitespace
               logit(90,"working on $ll $in_node $in_id");
               $sx = $snodex{$in_node};
               next if !defined $sx;
               next if $snode_agent_interested[$sx] == 0;
               $snode_agent_responsive[$sx] = 1
            } # next entries
         } # some entries
      } # bad soap return
      dumplog;
   } # next product
} # next TEMS

# if wanted, redo the non-responsive ones individually...
if ($opt_noretry == 0) {
   for (my $i=0; $i<=$snodei; $i++) {
      next if $snode_agent_interested[$i] == 0;
      next if $snode_agent_responsive[$i] == 1;
      logit(0,"working on agent[$snode[$i]] $i of $snodei");
      my $tlen = length($opt_agent_timeout);
#      $sSQL = "SELECT ID,DATETIME,ORIGINNODE FROM O4SRV.OPLOG AT('$snode_tems_thrunode[$i]') WHERE SYSTEM.PARMA('NODELIST','*ALL',4 ) AND SYSTEM.PARMA('TIMEOUT','$opt_retry_timeout',$tlen) AND ORIGINNODE = '$snode[$i]' AND FIRST(1);";
      $sSQL = "SELECT ID,DATETIME,ORIGINNODE FROM O4SRV.OPLOG AT('$snode_tems_thrunode[$i]') WHERE  SYSTEM.PARMA('TIMEOUT','$opt_retry_timeout',$tlen) AND ORIGINNODE = '$snode[$i]' AND FIRST(1);";
      @list = DoSoap("CT_Get",$sSQL);
      # note errors but continue on
      if ($run_status == 0) {
         if ($#list == 0) {
            foreach my $r (@list) {
               my $in_id = $r->{ID};
               $in_id =~ s/\s+$//;   #trim trailing whitespace
               $in_datetime = $r->{DATETIME};
               $in_datetime =~ s/\s+$//;   #trim trailing whitespace
               $in_node = $r->{System_Name};
               $in_node =~ s/\s+$//;   #trim trailing whitespace
               $snode_agent_responsive[$i] = 1;
               $snode_agent_retry[$i] = 1;
               $snode_agent_oplog1[$i] = $in_id if $in_id ne "KRALOG000";
            }
         }
      }
      dumplog;
   }
}


my $total_uninterested = 0;
my $total_nonresponsive = 0;
my $total_responsive = 0;
my $total_retries = 0;
my $total_oplog1 = 0;
my $rlinei = -1;
my @rline = ();
my $outline;

# now produce report
for (my $i=0; $i<=$snodei; $i++) {
   if ($snode_agent_interested[$i] == 0) {
      $total_uninterested += 1;
   } elsif ($snode_agent_responsive[$i] == 0) {
      $total_nonresponsive += 1;
      $outline = "$snode[$i],";
      $outline .= "$snode_tems_thrunode[$i],";
      $outline .= "$snode_tems_version[$i],";
      $outline .= "$snode_tems_product[$i],";
      $outline .= "$snode_agent_version[$i],";
      @words = split(";",$snode_agent_common[$i]);
      @words = split(":",$words[1]);
      my $p_ver = substr($words[0],2,8);
      $outline .= "$p_ver,";
      $outline .= "$snode_tems_hostaddr[$i],";
      $rlinei++;$rline[$rlinei]="$outline\n";
   } else {
      $total_responsive += 1;
      $total_retries += 1 if $snode_agent_retry[$i] == 1;
   }
}
$rlinei++;$rline[$rlinei]="\n";
if ($total_retries > 0) {
   $rlinei++;$rline[$rlinei]="Responsive agents with invalid oplog first line\n";
   $rlinei++;$rline[$rlinei]="Node,Thrunode,TEMS_version,Product,Agent_Version,TEMA_version,Oplog1,Hostaddr\n";
   for (my $i=0; $i<=$snodei; $i++) {
      next if $snode_agent_responsive[$i] == 0;
      next if $snode_agent_retry[$i] == 0;
      next if $snode_agent_oplog1[$i] eq "";
      $outline = "$snode[$i],";
      $outline .= "$snode_tems_thrunode[$i],";
      $outline .= "$snode_tems_version[$i],";
      $outline .= "$snode_tems_product[$i],";
      $outline .= "$snode_agent_version[$i],";
      @words = split(";",$snode_agent_common[$i]);
      @words = split(":",$words[1]);
      my $p_ver = substr($words[0],2,8);
      $outline .= "$p_ver,";
      $outline .= "$snode_agent_oplog1[$i],";
      $total_oplog1 += 1;
      $outline .= "$snode_tems_hostaddr[$i],";
      $rlinei++;$rline[$rlinei]="$outline\n";
   }
}


my $zombie_dur = time - $zombie_start;

open OH, ">$opt_o" or die "can't open '$opt_o': $!";
print OH "Zombie Agent Report $gVersion - duration $zombie_dur seconds\n";
print OH "Arguments $args_start\n";
print OH "\n";
my $psnodei = $snodei+1;
print OH "Total Managed systems,$psnodei,\n";
print OH "Total Responsive agents,$total_responsive,\n";
print OH "Total Responsive agents needing retry,$total_retries,\n";
print OH "Total Zombie agents,$total_nonresponsive,\n";
print OH "Total Invalid Oplog agents,$total_oplog1,\n";
print OH "\n";
print OH "Possible Zombie Agents\n";
print OH "Node,Thrunode,TEMS_version,Product,Agent_Version,TEMA_version,Hostaddr\n";

for (my $i=0; $i<=$rlinei; $i++) {
   print OH $rline[$i];
}
close OH;

dumplog;

exit 0;


# Get options from command line - which have first priority
sub init {
   my $myargs_remain;
   my @myargs_remain_array;
   use Getopt::Long qw(GetOptionsFromString);
   $myargs = shift;

   ($rc,$myargs_remain) = GetOptionsFromString($myargs,
              'log=s' => \ $opt_log,                  # log file
              'ini=s' => \ $opt_ini,                  # control file
              'user=s' => \$user,                     # userid
              'passwd=s' => \$passwd,                 # password
              'debuglevel=i' => \ $opt_debuglevel,    # log file contents control
              'agent_timeout=i' => \ $opt_agent_timeout, # Agent timeout
              'debug' => \ $opt_debug,                # log file contents control
              'h' => \ $opt_h,                        # help
              'v' => \  $opt_v,                       # verbose - print immediately as well as log
              'vt' => \  $opt_vt,                     # verbose traffic - print traffic.txt
              'noretry' => \  $opt_noretry,             # retry failures one by one
              'retry_timeout=i' => \ $opt_retry_timeout, # retry failures one by one
              'o=s' => \ $opt_o,                      # output file
              'pc=s' => \  @opt_pc,                   # Product Code
              'tems=s' => \  @opt_tems,               # TEMS names
              'dpr' => \ $opt_dpr,                    # dump data structures
              'std' => \ $opt_std                    # credentials from standard input
             );
   # if other things found on the command line - complain and quit
   @myargs_remain_array = @$myargs_remain;
   if ($#myargs_remain_array != -1) {
      foreach (@myargs_remain_array) {
        print STDERR "SURVEY001E Unrecognized command line option - $_\n";
      }
      print STDERR "SURVEY001E exiting after command line errors\n";
      exit 1;
   }

   # Folloowing are command line only defaults. All others can be set from the ini file

   if (!defined $opt_ini) {$opt_ini = "zombie.ini";}           # default control file if not specified
   if ($opt_h) {&GiveHelp;}  # GiveHelp and exit program
   if (!defined $opt_debuglevel) {$opt_debuglevel=90;}         # debug logging level - low number means fewer messages
   if (!defined $opt_debug) {$opt_debug=0;}                    # debug - turn on rare error cases

   # ini control file must be present

   unless (-e $opt_ini) {                                      # make sure ini file is present
      print STDERR "SURVEY002E Control ini file $opt_ini missing\n";
      exit 1;
   }

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
         if ($words[0] eq "debug") {$opt_debug = 1;}
         elsif ($words[0] eq "verbose") {$opt_v = 1;}
         elsif ($words[0] eq "traffic") {$opt_vt = 1;}
         elsif ($words[0] eq "std") {$opt_std = 1;}
         elsif ($words[0] eq "noretry") {$opt_noretry = 1;}
         elsif ($words[0] eq "passwd") {}                      # null password
         else {
            logit(0,"SURVEY003E Control without needed parameters $words[0] - $opt_ini [$l]");
            $run_status++;
         }
         next;
      }

      # two word controls - option and value
      if ($words[0] eq "soapurl") {push(@connections,$words[1]);}
      elsif ($words[0] eq "soap") {push(@connections,$words[1]);}
      elsif ($words[0] eq "user")  {$user = $words[1];}
      elsif ($words[0] eq "passwd")  {$passwd = $words[1];}
      elsif ($words[0] eq "log") {$opt_log = $words[1];}
      elsif ($words[0] eq "pc") {push(@opt_pc,$words[1]);}
      elsif ($words[0] eq "tems") {push(@opt_tems,$words[1]);}
      elsif ($words[0] eq "agent_timeout") {$opt_agent_timeout = $words[1];}
      elsif ($words[0] eq "retry_timeout") {$opt_retry_timeout = $words[1];}
      elsif ($words[0] eq "o") {$opt_o = $words[1];}
      elsif ($words[0] eq "soap_timeout") {$opt_soap_timeout = $words[1];}
      else {
         logit(0,"SURVEY005E ini file $l - unknown control $words[0]"); # kill process after current phase
         $run_status++;
      }
   }

   # defaults for options not set otherwise

   if (!defined $opt_log) {$opt_log = "zombie.log";}           # default log file if not specified
   if (!defined $opt_h) {$opt_h=0;}                            # help flag
   if (!defined $opt_v) {$opt_v=0;}                            # verbose flag
   if (!defined $opt_vt) {$opt_vt=0;}                          # verbose traffic default off
   if (!defined $opt_dpr) {$opt_dpr=0;}                        # data dump flag
   if (!defined $opt_std) {$opt_std=0;}                        # default - no credentials in stdin
   if (!defined $opt_agent_timeout) {$opt_agent_timeout=50;}   # default 50 seconds
   if (!defined $opt_soap_timeout) {$opt_soap_timeout=180;}    # default 180 seconds
   if (!defined $opt_noretry) {$opt_noretry=0;}                  # default to retry
   if (!defined $opt_retry_timeout) {$opt_retry_timeout=15;}           # default 15 second retry
   if (!defined $opt_o) {$opt_o="zombie.csv";}                 # default output file


   # collect the TEMSes information into an array
   foreach my $t (@opt_tems) {$opt_temsx{$t} = 1;}

   # same thing for product codes [agent types] except upper case the values first

   if ($#opt_pc != -1) {
      my $t = join(" ",@opt_pc);
      $t = uc $t;
      @opt_pc = split(" ",$t);
   }

   foreach my $t (@opt_pc) {$opt_pcx{$t} = 1;}

   if ($opt_dpr == 1) {
      my $module = "Data::Dumper";
      eval {load $module};
      if ($@) {
         logit(1,"Cannot load Data::Dumper - ignoring -dpr option");
         $opt_dpr = 0;
      }
   }

   # if credential as passed in via standard input, then that takes precendence.

   if ($opt_std == 1) {
      my $stdline = <STDIN>;
      if (defined $stdline) {
         my @values = split(" ",$stdline);
         while (@values) {
            if ($values[0] eq "-user")  {
               shift(@values);
               $user = shift(@values);
               die "STD option -user with no following value\n" if !defined $user;
            } elsif ($values[0] eq "-passwd")  {
               shift(@values);
               $passwd = shift(@values);
               die "STD option -passwd with no following value\n" if !defined $passwd;
            } else {
               my $rest_stdin = join(" ",@values);
               die "unknown option(s) in stdin [$rest_stdin]\n" if defined $rest_stdin;
            }
         }
      }
   }

   # complain about options which must be present

   if ($#connections == -1) {
      logit(0,"SURVEY006E connection missing in ini file $opt_ini");
      $run_status++;
   }
   if ($user eq "") {
      logit(0,"SURVEY007E user missing in ini file $opt_ini or stdin");
      $run_status++;
   }

   # if any errors, then dump log and exit
   # this way we can show multiple errors at startup
   if ($run_status) { dumplogexit;}

}

sub tems_node_analysis
{
   $survey_tems++;

   # local variables
   my $node_filebase;


   # reset all variables used by the tems static analysis
   @sitnames     = ();
   %sitnamex     = ();
   @sitobjaccl   = ();
   @situadaccl   = ();
   %objcobj = ();

   $nodli = -1;
   @snodlnames = ();
   %snodlx = ();
   @snodlnodes = ();

   $snodei = -1;
   @snode = ();
   %snodex = ();
   %snode_filex = ();
   @snode_survey_online = ();                  # used to track offline conditions
   @snode_survey_sits = ();
   @snode_persist_sits = ();
   @snode_survey_sits_noauto = ();
   @snode_tems_product = ();
   @snode_tems_thrunode = ();
   @snode_tems_version = ();
   @snode_tems_hostaddr = ();
   @snode_agent_version = ();                  # version  information, include ip address
   @snode_agent_common  = ();                  # common software levels
   @snode_survey_maxdelay = ();
   @snode_survey_maxdelay_situation = ();
   @snode_survey_connects = ();
   @snode_survey_sitct = ();
   @snode_survey_actions = ();
   @snode_agent_responsive = ();               # when 1, node was responsive
   @snode_agent_interested = ();               # when 1, node is being checked
   @snode_agent_retry      = ();               # when 1, retry used
   @snode_agent_oplog1     = ();               # when non-null, invalid first oplog record

   $temsi = -1;
   @tems = ();
   %temsx = ();
   @tems_thrunode = ();
   @tems_version = ();                         # version
   @tems_vmsize = ();                          # current process size
   @tems_cpubusy = ();                         # current process cpubusy
   @tems_server_busy = ();                     # current server cpubusy
   @tems_hostaddr = ();                        # current TEMS host address
   @tems_time = ();
   @tems_time_epoch = ();
   @tems_time_capture = ();
   $temsat = "";

   # variables for tracking situation groups.


   # variables for getting product information from the node status table

   $prodi = -1;
   @prodnames = ();
   %prodx = ();
   @prodsits = ();


   # variables for calculating the UADVISOR situations and situations with commands

   my $name;

   # get names of online TEMSes
   $sSQL = "SELECT NODE,THRUNODE,HOSTADDR,VERSION,HOSTINFO FROM O4SRV.INODESTS WHERE O4ONLINE='Y' AND PRODUCT='EM'";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}

   foreach my $r (@list) {
       $node = $r->{NODE};
       $node =~ s/\s+$//;   #trim trailing whitespace
       $temsi++;
       $tx = $temsi;
       $tems[$tx] = $node;
       $temsx{$node} = $tx;
       my $thrunode = $r->{'THRUNODE'};
       $thrunode =~ s/\s+$//;   #trim trailing whitespace
       $tems_thrunode[$tx] = $thrunode;
       $tems_version[$tx] = $r->{'VERSION'};
       my $hostaddr;
       $rt = ref($r->{HOSTADDR});
       if ($rt eq "HASH") {
          $hostaddr = $r->{HOSTADDR}->{'IP.PIPE'};
          $hostaddr = $r->{HOSTADDR}->{'IP.SPIPE'} if !defined $hostaddr;
       } else {
          $hostaddr = $r->{HOSTADDR};
       }
       $hostaddr =~ s/\s+$//;   #trim trailing whitespace
       $tems_hub_nodeid = $node if $node eq $thrunode;
       $tems_hostaddr[$tx] = $hostaddr;
       $tems_time[$tx] = 0;
       $tems_time_capture[$tx] = 0;
       $tems_vmsize[$tx] = 0;
       $tems_cpubusy[$tx] = 0;
       $tems_server_busy[$tx] = 0;
   }


   # determine if any TEMSes are non-responsive
   for (my $i=0;$i<=$temsi;$i++) {
      $sSQL = "SELECT SYSTIME FROM O4SRV.UTCTIME AT(\'$tems[$i]\')";
      @list = DoSoap("CT_Get",$sSQL);
      if ($run_status) {
         $s_errcode = 101;
         $s_erritem = "Timeout(TEMS)";
         $s_errtext = "TEMS $tems[$i] TEMS Get time - run status [$run_status]";
         logit(0,$s_errtext);
         next;
      }
      if ($#list == -1) {
         $s_errcode = 102;
         $s_erritem = "NoData(TEMS)";
         $s_errtext = "TEMS $tems[$i] TEMS Get time - no data";
         logit(0,$s_errtext);
         next;
      }
      $tems_time[$i] = $list[0]->{Timestamp};
      $tems_time_epoch[$i] = get_ITM_epoch($list[0]->{Timestamp});
      $tems_time_capture[$i] = time;
   }

   # calculate list of operational TEMSes that responded with a time.
   for (my $i = 0; $i <=$temsi; $i++) {
      next if $tems_time[$i] == 0;
      if ($temsat eq "") { $temsat = "AT('";} else {$temsat .= ",'";}
     $temsat .= $tems[$i] . "'";
   }
   $temsat .= ")";

   # get node status for online managed systems
   my $samp_nodes = "";    #prepare for nodelist capture

#  $sSQL = "SELECT NODE, THRUNODE, PRODUCT, HOSTADDR, VERSION, RESERVED FROM O4SRV.INODESTS WHERE O4ONLINE='Y' AND PRODUCT <> 'EM' AND FIRST(175)";  # debug
   $sSQL = "SELECT NODE, THRUNODE, PRODUCT, HOSTADDR, VERSION, RESERVED FROM O4SRV.INODESTS WHERE O4ONLINE='Y' AND PRODUCT <> 'EM'";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}

   $ll = 0;
   $pcount = $#list+1;
   foreach my $r (@list) {
       $ll++;
       my $count = scalar(keys %$r);
       if ($count < 6) {
          logit(10,"working on INODESTS row $ll of $pcount has $count instead of expected 6 keys");
          next;
       }
       $node = $r->{NODE};
       $node =~ s/\s+$//;   #trim trailing whitespace
       my $thrunode = $r->{THRUNODE};
       $thrunode =~ s/\s+$//;   #trim trailing whitespace
       $product = $r->{PRODUCT};
       $product =~ s/\s+$//;   #trim trailing whitespace
       my $hostaddr = $r->{HOSTADDR};
       $hostaddr =~ s/\s+$//;   #trim trailing whitespace
       my $agent_version = $r->{VERSION};
       $agent_version =~ s/\s+$//;   #trim trailing whitespace
       my $agent_common = $r->{RESERVED};
       $agent_common =~ s/\s+$//;   #trim trailing whitespace
       $ptx = $temsx{$thrunode};    #ignore any agents not connected through TEMSes
       next if !defined $ptx;       # the subnode agents

       $snodei++;
       $snx = $snodei;
       $snode[$snx] = $node;
       $snodex{$node} = $snx;
       $node_filebase = $node;
       $node_filebase =~ s/:/_/g;
       $snode_filex{$node_filebase} = $snx;
       $snode_survey_online[$snx] = 1;                    # node online when we checked the TEMS tables
       $snode_survey_sits[$snx] = " ";
       $snode_persist_sits[$snx] = " ";
       $snode_survey_sits_noauto[$snx] = " ";
       $snode_tems_product[$snx] = $product;
       $snode_tems_hostaddr[$snx] = $hostaddr;
       $snode_tems_thrunode[$snx] = $thrunode;
       $snode_agent_version[$snx] = $agent_version;
       $snode_tems_version[$snx] = "";
       $ptx = $temsx{$thrunode};
       $snode_tems_version[$snx] = $tems_version[$ptx] if defined $ptx;
       $snode_agent_common[$snx] = $agent_common;
       $snode_agent_responsive[$snx] = 0;           # non-responsive until tested
       $snode_agent_interested[$snx] = 1;           # interested unless product values set
       $snode_agent_retry[$snx]      = 0;           # When 1, retry performed
       $snode_agent_oplog1[$snx]     = "";          # invalid first oplog entry
       if ($#opt_pc != -1) {                        # if product codes set, only interested in those
          $ptx = $opt_pcx{$product};
          $snode_agent_interested[$snx] = 0 if !defined $ptx;
       }
       if ($#opt_tems != -1) {
          $ptx = $opt_temsx{$thrunode};
          $snode_agent_interested[$snx] = 0 if !defined $ptx;
       }

       $ptx = $temsx{$thrunode};
       $snode_agent_interested[$snx] = 0 if $tems_time[$ptx] == 0;

       # record the first agent for each product type. Will be used to determine system generated
       # managed systemlist later on.
       $ptx = $xprodx{$product};
       if (!defined $ptx) {
          $xprodi++;
          $ptx = $xprodi;
          $xprod[$ptx] = $product;
          $xprodx{$product} = $ptx;
          $xprodn{$node} = $ptx;
          $xprod_agent[$ptx] = $node;
          $xprod_msl[$ptx] = "";
          if ($samp_nodes eq "") {
             $samp_nodes .= "NODE='$node'";
          } else {
             $samp_nodes .= " OR NODE='$node'";
          }
       }

       # keep track of the number of products of each type at each TEMS
       # No sense in asking for data when there is none there
       $key = $thrunode . "_" . $product;
       $ptx = $pxprodx{$key};
       if (!defined $ptx) {
          $pxprodi++;
          $ptx = $pxprodi;
          $pxprod[$ptx] = $key;
          $pxprodx{$key} = $ptx;
          $pxprod_count[$ptx] = 0;
       }
       $pxprod_count[$ptx] += 1;
       logit(100,"Node $snodei $node product[$snode_tems_product[$snx]] thrunode[[$snode_tems_thrunode[$snx]] hostaddr[[$snode_tems_hostaddr[$snx]]  agent_version[$snode_agent_version[$snx]]  agent_common[$snode_agent_common[$snx]]");
   }
   # Get TNODELST data to figure out what the system generated MSL name is for each product
   $sSQL = "SELECT NODE, NODELIST, NODETYPE FROM O4SRV.TNODELST WHERE $samp_nodes AND NODETYPE='M'";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}
   $ll = 0;
   $pcount = $#list+1;
   foreach my $r (@list) {
       $ll++;
       my $count = scalar(keys %$r);
       if ($count < 3) {
          logit(10,"working on TNODELST results row $ll of $pcount has $count instead of expected 3 keys");
          next;
       }
       $node = $r->{NODE};
       $node =~ s/\s+$//;   #trim trailing whitespace
       $nodelist = $r->{NODELIST};
       $nodelist =~ s/\s+$//;   #trim trailing whitespace
       next if substr($nodelist,0,1) ne "*";
       $ptx = $xprodn{$node};
       $xprod_msl[$ptx] = $nodelist if defined $ptx;
   }

  dumplog;
  @log = ();
}



#------------------------------------------------------------------------------
# Perform soap process
#------------------------------------------------------------------------------
sub DoSoap
{
   $survey_sqls++;                             # keep count of SQLs
   $soap_faultstr = "";                             # reset fault string to null
   $soap_faultcode = "";                            # reset fault code to null
   my @results2;
   my $sql_start_time = time;
   my $mySQL;
   my $get_raw;
   my $res;
   my $result;

   my $soap_action = shift;
   if ($soap_action eq "CT_Get") {
      $mySQL = shift;

      my @aParms = (
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(table => 'O4SRV.UTCTIME' ),
         SOAP::Data->name(sql => $mySQL )
      );

      logit(10,"SOAP CT_Get start - $mySQL");
      $res = $oHub->CT_Get(@aParms);
      $soap_rc = $?;
      $survey_sql_time += time - $sql_start_time;
      logit(10,"SOAP CT_Get end [$soap_rc] - $mySQL");

   } elsif ($soap_action eq "CT_Get_Object") {
      $mySQL = shift;
      $get_raw = shift;
      $get_raw = "" if !defined $get_raw;

      my @aParms = (
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(object => $mySQL )
      );

      logit(10,"SOAP CT_Get_Object start - $mySQL");
      $res = $oHub->CT_Get(@aParms);
      $soap_rc = $?;
      $survey_sql_time += time - $sql_start_time;
#     sleep 10;
      logit(10,"SOAP CT_Get_Object end [$soap_rc] - $mySQL");
      return $res if $get_raw eq 'raw';                 # use raw return

   } elsif ($soap_action eq "CT_Alert") {
      my $myAlert_name = shift;
      my $myAlert_source = shift;
      my $myAlert_item = shift;
      my $myAlert_timestamp = shift;

      my @aParms = (
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(name =>      $myAlert_name),
         SOAP::Data->name(source =>    $myAlert_source),
         SOAP::Data->name(item =>      $myAlert_item),
         SOAP::Data->name(timestamp => $myAlert_timestamp),
         SOAP::Data->name(results =>   '~')
      );

      logit(10,"SOAP Alert start - $myAlert_name $myAlert_source $myAlert_item $myAlert_timestamp");
      $res = $oHub->CT_Alert(@aParms);
      $soap_rc = $?;
      logit(10,"SOAP Alert end [$soap_rc]");

   } elsif ($soap_action eq "CT_Reset") {
      my $myAlert_name = shift;
      my $myAlert_source = shift;
      my $myAlert_item = shift;
      my $myAlert_timestamp = shift;

      my @aParms = (
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(name =>      $myAlert_name),
         SOAP::Data->name(source =>    $myAlert_source),
         SOAP::Data->name(item =>      $myAlert_item),
         SOAP::Data->name(timestamp => $myAlert_timestamp),
         SOAP::Data->name(results =>   '~')
      );

      logit(10,"SOAP Reset start - $myAlert_name $myAlert_source $myAlert_item $myAlert_timestamp");
      $res = $oHub->CT_Reset(@aParms);
      $soap_rc = $?;
      #$survey_sql_time += time - $sql_start_time;
      logit(10,"SOAP Reset end [$soap_rc]");

   } else {
      logit(0,"Unknown SOAP message [$soap_action]");
      dumplogexit;
  }

if ($soap_rc != 0) {
   # note this possible message "read timeout at C:/Perl/site/lib/LWP/Protocol/http.pm line 433."
   # for timeout cases. Possibly want to retry at some point.
   $soap_faultstr = chop($res);
   logit(0,"ERROR $soap_rc Problem submitting SOAP Call - $soap_faultstr");
   $run_status++;
   return @results2;
}
if (substr($res,0,1) ne "<") {
   $soap_faultstr = $res;
   logit(0,"ERROR $soap_rc SOAP Failure - $soap_faultstr");
   $run_status++;
   return @results2;
}

if (substr($res,0,6) eq "<HTML>") {
   $soap_faultstr = $res;
   logit(0,"ERROR $soap_rc non-SOAP response - $soap_faultstr");
   $run_status++;
   return @results2;
}

#  print STDERR "INFO" . "SOAP Call submitted successfully\n";
if (91 <= $opt_debuglevel) {
   logit(91,"INFO result res[$res]");
   dumplog;
   @log = ();
}

if ($opt_dpr == 1) {
   if (91 <= $opt_debuglevel) {
      dumplog;
      @log = ();
      datadumperlog("Data:Dumper of \$res","$res");
   }
}

#

# the eval is needed to trap some illegal soap syntax and save for later analysis
eval {$result = $tpp->parse($res);};
if ($@) {
   $soap_faultstr = $@;
   logit(0,"ERROR syntax error detected by XML::Simple in the XMLin() routine");
   logit(0,"$@");
   logit(0,"INFO result res[$res]");
   $run_status++;
   return @results2;
}

if ($opt_dpr == 1) {
   if (91 <= $opt_debuglevel) {
      dumplog;
      @log = ();
      datadumperlog("Data:Dumper of \$result","\$result");
   }
}

# Check for an error fault return. Call out a login failure immediately.
# pretty much any error here prevents data retrieval, stop trying

$rt = ref($result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-ENV:Fault'});
if ($rt eq "HASH") {
      $soap_faultstr = $result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-ENV:Fault'}->{'faultstring'};
      $soap_faultcode = $result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-ENV:Fault'}->{'faultcode'};
      logit(0,"ERROR SOAP - $soap_faultcode $soap_faultstr");
      if ($soap_faultstr eq "CMS logon validation failed.") {
         dumplog;
         die "Logon userid/password invalid, please correct" if $soap_faultstr eq "CMS logon validation failed.";
      }
      $run_status++;
} else {
   if ($soap_action eq "CT_Get_Object") {
     if ($result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{'OBJECT'} eq "Local_System_Command") {
         return @results2;
     }
   }
   $rt = ref($result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW});                                       #
   if ($rt eq "ARRAY") {
      @results2=@{$result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW}};
   }
   elsif ($rt eq "HASH") {
       push(@results2,$result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW});
   }
   else {       # check if data contained in an envelope
      $rt = ref($result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW});                                       #
      if ($rt eq "ARRAY") {
         @results2=@{$result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW}};
      }
      elsif ($rt eq "HASH") {
         push(@results2,$result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW});
      } else {
         $soap_faultstr = $res;
         logit(0,"ERROR SOAP no data  - $soap_faultstr");
         logit(0,"unknown result type [$rt] processing SOAP Call for $mySQL - missing data");
      }
   }
}

if ($opt_dpr == 1) {
   if (91 <= $opt_debuglevel) {
      dumplog;
      @log = ();
      datadumperlog("Data:Dumper of \@results2","\@results2");
   }
}

return @results2;
}

#------------------------------------------------------------------------------
sub GiveHelp
{
  $0 =~ s|(.*)/([^/]*)|$2|;
  print <<"EndOFHelp";

  $0 v$gVersion

  This script surveys an ITM environment looking agents which are
  online but possible not responsive.

  Default values:
    log          : zombie.log
    ini          : zombie.ini
    user         : <none>
    passwd       : <none>
    debuglevel   : 90 [considerable number of messages]
    debug        : 0  when 1 some breakpoints are enabled]
    h            : 0  display help information
    v            : 0  display log messages on console
    vt           : 0  record http traffic on traffic.txt file
    pc           : product code of agents - can supply multiple codes
    tems         : tems the agents report to - can supply multiple code
    dpr          : 0  dump data structure if Dump::Data installed
    std          : 0  get user/password from stardard input
    agent        : <none> single agent survey and then stop
    agent_timeout : seconds to wait for an agent response, default 50 seconds
    noretry       : after a stage I failure, skip the retry on individual agents, default off
    retry_timeout : Agent timeout during retry - default 15 seconds

  Example invovation
    $0  -ini <control file> -pc ux

  Note: $0 uses an initialization file [default survey.ini] for many controls.

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
      push(@log, $oline);
      print $oline . "\n" if $opt_v == 1;
   }
}

#------------------------------------------------------------------------------
# capture agent log record
#------------------------------------------------------------------------------
# capture agent error record
sub dumplogexit
{
   logit(0,"SURVEY999E - total runtime errors = $run_status");
   dumplog;
   exit 1;
}

# write output log
sub dumplog
{
   open FH, ">>$opt_log" or die "can't open '$opt_log': $!";
   foreach ( @log ) { print FH $_ . "\n";}
   close FH;
   @log = ();
}

# write output log
sub datadumperlog
{
   require Data::Dumper;
   my $dd_msg = shift;
   my $dd_var = shift;
   open FH, ">>$opt_log" or die "can't open '$opt_log': $!";
   print FH "$dd_msg\n";
   no strict;
   print FH Data::Dumper->Dumper($dd_var);
   close FH;
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
sub get_timestamp {
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
   $year += 1900;
   $mon += 1;


   my $nyy = substr("00" . $year,-2,2);
   my $nmo = substr("00" . $mon,-2,2);
   my $ndd = substr("00" . $mday,-2,2);
   my $nhh = substr("00" . $hour,-2,2);
   my $nmm = substr("00" . $min,-2,2);
   my $nss = substr("00" . $sec,-2,2);

   my $etime = "1" . $nyy . $nmo . $ndd . $nhh . $nmm . $nss . "000";  # check time in ITM 16 byte format
   return $etime;
}

# get current epoch in seconds from ITM standard timestamp form
sub get_ITM_epoch {
   my $itm_stamp = shift;
#(my $icc, my $iyy, my $imo, my $idd, my $ihh, my $imm, my $iss) = unpack("A1 A2 A2 A2 A2 A2 A2",$itm_stamp);
(my $iyy, my $imo, my $idd, my $ihh, my $imm, my $iss) = unpack("A2 A2 A2 A2 A2 A2",substr($itm_stamp,1));

my $dt0 = DateTime->new(year=>"20" . $iyy,
                       month=>$imo,
                       day=>$idd,
                       hour=>$ihh,
                       minute=>$imm,
                       second=>$iss);
return $dt0->epoch();
}

# calculate with timestamps

sub calc_timestamp {
   my $instamp = shift;
   my $infunc = shift;
   my $indelta = shift;
   my $outstamp;

   my $dt0 = DateTime->new(year=>"20" . substr($instamp,1,2),
                          month=>substr($instamp,3,2),
                          day=>substr($instamp,5,2),
                          hour=>substr($instamp,7,2),
                          minute=>substr($instamp,9,2),
                          second=>substr($instamp,11,2));

   my $dt = $dt0->clone();
   if ($infunc eq "-") {
      $dt = $dt->subtract(seconds=>$indelta);
   } else {
      $dt = $dt->add(seconds=>$indelta);
   }

   # return calculated time in ITM 16 byte format
   $outstamp = "1" . substr("00" . $dt->year,-2,2) . substr("00" . $dt->month,-2,2) . substr("00" . $dt->day,-2,2) . substr("00" . $dt->hour,-2,2) . substr("00" . $dt->minute,-2,2)  . substr("00" . $dt->second,-2,2) . "000";
   return $outstamp;
}

# Following logic replicates most of the tacmd processing logic to determine the
# protocol and port number required to access ITM Web Services or SOAP. For input
# it uses the soapurl supplied by the user. From this the following is discovered
#   1) Is a forced protocol supplied  - https or http
#   2) Is a port number supplied
# The natural SOAP URL will be accessed using a remote command with no content. That will verify the userid and password.
# If an error results, then the index.xml file is retrieved and parsed to determine if there is a better port to use
# There are various error conditions that can result and will cause a failure. The most common case
# is be a TEMS behind a firewall that only allows port 3661 access. If the hub TEMS is recycled, the SOAP access
# port would be an ephemeral one. The port number could be discovered in the index.xml data but access would fail.
# In any case, an error message will show what needs to be done.

# SOAP::Lite does not support http6 or https6 at the current level and so that processing is present but
# blocked at present.

sub get_connection {
my $opt_soap_lite_v6 = 0;            # Change to 1 when SOAP::Lite supports http6 and https6
                                     # This allows the support for http6/https6 to be present but not effect processing
my $connect_protocolGiven = 0;       # when 1, soapurl contains a known protocol
my $connect_portGiven = 0;           # when 1, soapurl contains a port number
my $connect_attempthttps = 0;        # when 1, attempt access by https
my $connect_attempthttps6 = 0;       # when 1, attempt access by https6 [ future SOAP::Lite ]
my $connect_attempthttp = 0;         # when 1, attempt access by http
my $connect_attempthttp6 = 0;        # when 1, attempt access by http6  [ future SOAP::Lite ]
my $connect_httpPortNo = "";         # http port number found in index.xml results
my $connect_httpsPortNo = "";        # https port number found in index.xml results
my $connect_ip6PortNo = "";          # http6 port number found in index.xml results   [ future SOAP::Lite ]
my $connect_ips6PortNo = "";         # https6 port number found in index.xml results  [ future SOAP::Lite ]
my $connect_rest;                    # section of soapurl with protocol removed
my $connect_hostName;                # section of soapurl identified as hostname [or ip address] of the server running hub TEMS
my $connect_port;                    # port used to access SOAP server
my $connect_protocol;                # protocol used to access SOAP
my $connect_res;                     # results returned from SOAP
my $test_connection;                 # trial connection string
my $connect_httpsFound;              # during index.xml analysis, https port found
my $connect_httpFound;               # during index.xml analysis, http port found
my $connect_https6Found;             # during index.xml analysis, https6 port found [ future SOAP::Lite ]
my $connect_http6Found;              # during index.xml analysis, http6 port found  [ future SOAP::Lite ]
my $result;
my @results3;                        # array used in parsing top level index.xml results
my @results4;                        # array used in parsing second level index.xml results
my $in_protocol;                     # protocol from index.xml results

   logit(0,"Determine proper SOAP connection based on [$connection]");

   # stage 1, analyze the given connection string

   if (substr($connection,0,8) eq "https://") {                           # user supplied https
      $connect_protocol = "https";
      $connect_attempthttps = 1;
      $connect_attempthttps6 = 1 if $opt_soap_lite_v6 == 1;
      $connect_protocolGiven = 1;
      $connect_rest = substr($connection,8);

   } elsif (substr($connection,0,9) eq "https6://") {                     # user supplied https6, future SOAP::Lite logic
      $DB::single=2 if $opt_debug == 1;
      next unless $opt_soap_lite_v6 == 1;
      $connect_protocol = "https6";
      $connect_attempthttps6 = 1;
      $connect_protocolGiven = 1;
      $connect_rest = substr($connection,9);

   } elsif (substr($connection,0,7) eq "http://") {                       # user supplied http
      $connect_protocol = "http";
      $connect_attempthttp = 1;
      $connect_attempthttp6 = 1 if $opt_soap_lite_v6 == 1;
      $connect_protocolGiven = 1;
      $connect_rest = substr($connection,7);

   } elsif (substr($connection,0,8) eq "http6://") {                      # user supplied http6, future SOAP::Lite logic
      $DB::single=2 if $opt_debug == 1;
      next unless $opt_soap_lite_v6 == 1;
      $connect_protocol = "http6";
      $connect_attempthttp6 = 1;
      $connect_protocolGiven = 1;
      $connect_rest = substr($connection,8);

   } else {
      $connect_attempthttps = 1;                                          # user did not supply protocol, try https and then http
      $connect_attempthttps6 = 1 if $opt_soap_lite_v6 == 1;
      $connect_attempthttp = 1;
      $connect_attempthttp6 = 1 if $opt_soap_lite_v6 == 1;
      $connect_rest = $connection;
   }

   # Stage 2, get the port number if one supplied
   if (index($connect_rest,':') != -1) {
      $connect_rest =~ m/(\S+):(\d+)/;
      $connect_hostName = $1;
      $connect_port = $2;
      $connect_portGiven = 1;
   } else {
      $connect_hostName = $connect_rest;
      $connect_port = "";
   }

   # stage 3, if port number was given but not protocol
   #           if port is associated with protocol then select that protocol
   #           otherwise try https and then http

   if (($connect_port ne "") and  ($connect_protocolGiven == 0)) {
      if ($connect_port == 3661) {
         $connect_attempthttp = 0;
         $connect_attempthttps = 1;
         $connect_attempthttps6 = 1 if $opt_soap_lite_v6 == 1;

      } elsif ($connect_port == 1920) {
         $connect_attempthttp = 1;
         $connect_attempthttps = 0;
         $connect_attempthttp6 = 1 if $opt_soap_lite_v6 == 1;

      } else {
         $connect_attempthttps = 1;
         $connect_attempthttps6 = 1 if $opt_soap_lite_v6 == 1;
         $connect_attempthttp = 1;
         $connect_attempthttp6 = 1 if $opt_soap_lite_v6 == 1;
      }
   }

   # Stage 4 create trial connection string based on attempt settings

   for (my $i=0; $i < 4; $i++) {
      if (($i == 0) and ($connect_attempthttps == 1)) {
         $connect_protocol = 'https' if $connect_protocolGiven == 0;
         $connect_port = '3661' if $connect_portGiven == 0;
      } elsif (($i == 1) and ($connect_attempthttps6 == 1)) {
         $DB::single=2 if $opt_debug == 1;
         $connect_protocol = 'https6' if $connect_protocolGiven == 0;
         $connect_port = '3661' if $connect_portGiven == 0;
      } elsif (($i == 2) and ($connect_attempthttp == 1)) {
         $connect_protocol = 'http' if $connect_protocolGiven == 0;
         $connect_port = '1920' if $connect_portGiven == 0;
      } elsif (($i == 3) and ($connect_attempthttp6 == 1)) {
         $DB::single=2 if $opt_debug == 1;
         $connect_protocol = 'https6' if $connect_protocolGiven == 0;
         $connect_protocol = 'http6' if $connect_protocolGiven == 0;
         $connect_port = '1920' if $connect_portGiven == 0;
      } else {
         next;
      }
      $test_connection = $connect_protocol . "://" . $connect_hostName . ":" . $connect_port . "///cms/soap";
      logit(0,"Trial SOAP connection based on [$test_connection]");
      $oHub = SOAP::Lite->proxy($test_connection,timeout => $opt_soap_timeout);          # set Soap::Lite controls
      $oHub->outputxml('true');                                                               # require xml output
      $oHub->on_fault( sub {});      # pass back all errors                                   # pass back error conditions
      $connect_res = DoSoap('CT_Get_Object','Local_System_Command');                          # attempt connection
      $run_status = 0;                                                                        # reset failure counter, since only resting
      if ($soap_rc == 0) {                                                                         # if good return code and empty fault string, then declare success
         if ($soap_faultstr eq "") {
            logit(0,"SOAP connection success [$test_connection]");
            $connection = $test_connection;
            return 0;
         }
      }

      # Prior to ITM 6.2, there was different logic. At the moment this is not supported.
      # For the record the logic looked in the results and did the following
      #   search for "Service Point"
      #   look ahead for <  and find sevice name within <>
      #   ignore if not "cms"
      #   look ahead for ":"
      #   look ahead for second ":"
      #   select characters until "/"
      #   result is alternate port number
      # try that as alternate port to access SOAP
   }

   # if not successful yet, work by retrieving the index.xml file
   #  This contains full information about what services are registered and the port number

   logit(0,"Trial SOAP connection failed, work with index.xml file");
   for (my $i=0; $i < 4; $i++) {
      if (($i == 0) and ($connect_attempthttps == 1)) {
         $connect_protocol = 'https' if $connect_protocolGiven == 0;
         $connect_port = '3661' if $connect_portGiven == 0;

      } elsif (($i == 1) and ($connect_attempthttps6 == 1)) {
         $DB::single=2 if $opt_debug == 1;
         $connect_protocol = 'https6' if $connect_protocolGiven == 0;
         $connect_port = '3661' if $connect_portGiven == 0;

      } elsif (($i == 2) and ($connect_attempthttp == 1)) {
         $connect_protocol = 'http' if $connect_protocolGiven == 0;
         $connect_port = '1920' if $connect_portGiven == 0;

      } elsif (($i == 3) and ($connect_attempthttp6 == 1)) {
         $DB::single=2 if $opt_debug == 1;
         $connect_protocol = 'http6' if $connect_protocolGiven == 0;
         $connect_port = '1920' if $connect_portGiven == 0;
      } else {
         next;
      }

      $test_connection = $connect_protocol . "://" . $connect_hostName . ":" . $connect_port . "/kdh/index/index.xml";
      logit(0,"Attempt retrievel of index.xml file using [$test_connection]");
      $oHub = SOAP::Lite->proxy($test_connection,timeout => $opt_soap_timeout);
      $oHub->outputxml('true');
      $oHub->on_fault( sub {});      # pass back all errors
      $connect_res = DoSoap('CT_Get_Object','Local_System_Command','raw');       # the 'raw' third parm means that DoSoap will not analyze results
      $run_status = 0;                                                           # reset error count
      next if $soap_rc != 0;                                                          # if severe error
      next if $soap_faultstr ne "";                                                   # or soap_faultstring, then exit
      next if substr($connect_res,0,1) ne '<';                                   # something bad happenned like timeout, ignore it

      eval {$result = $tpp->parse($connect_res)};                                # attempt to parse results
      if ($@ ne "") {
         logit(100,"error parsing index.xml results $@");
         next;
      }

      next if ref($result->{'kdh:servicepointlist'}->{'servicepoint'}) ne "ARRAY";  # array expected, else quit

      push(@results3,@{$result->{'kdh:servicepointlist'}->{'servicepoint'}});

      $connect_httpPortNo = "";                                                 # reset all potential results
      $connect_httpsPortNo = "";
      $connect_ip6PortNo = "";
      $connect_ips6PortNo = "";
      $connect_httpsFound = 0;
      $connect_httpFound = 0;
      $connect_https6Found = 0;
      $connect_http6Found = 0;

      foreach my $rr (@results3) {                                               # top level scan of services, looking for one that ends up "_cms"
         next if substr($rr->{'#text'},-4,4) ne '_cms';
         push(@results4,@{$rr->{'location'}->{'protocol'}});                     # capture protocol array
         foreach my $ss (@results4) {
            $in_protocol = $ss->{'#text'};
            if ($in_protocol eq "ip.ssl") {
               $DB::single=2 if $opt_debug == 1;
               $connect_httpsPortNo = $ss->{'endpoint'};
               $connect_httpsFound = 1;
            } elsif ($in_protocol eq "ip.tcp") {
               $connect_httpPortNo = $ss->{'endpoint'};
               $connect_httpFound = 1;
            } elsif ($in_protocol eq "ip6.ssl") {
               $DB::single=2 if $opt_debug == 1;
               next unless $opt_soap_lite_v6 == 1;
               $connect_ips6PortNo = $ss->{'endpoint'};
               $connect_https6Found = 1;
            } elsif ($in_protocol eq "ip6.tcpl") {
               $DB::single=2 if $opt_debug == 1;
               next unless $opt_soap_lite_v6 == 1;
               $connect_ip6PortNo = $ss->{'endpoint'};
               $connect_http6Found = 1;
            }
         }
      }

      # update the attempt variables based on the ports found
      $connect_attempthttps = 0;
      $connect_attempthttp  = 0;
      $connect_attempthttps6  = 0;
      $connect_attempthttp6  = 0;
      $connect_attempthttps = 1 if $connect_httpsPortNo ne "";
      $connect_attempthttp  = 1 if $connect_httpPortNo ne "";
      $connect_attempthttps6  = 1 if $connect_ips6PortNo ne "";
      $connect_attempthttp6  = 1 if $connect_ip6PortNo ne "";

      for (my $i=0; $i < 4; $i++) {
         if (($i == 0) and ($connect_attempthttps == 1)) {
            $DB::single=2 if $opt_debug == 1;
            $connect_protocol = 'https';
            $connect_port = $connect_httpsPortNo;
         } elsif (($i == 1) and ($connect_attempthttps6 == 1)) {
            $DB::single=2 if $opt_debug == 1;
            next unless $opt_soap_lite_v6 == 1;
            $connect_protocol = 'https6';
            $connect_port = $connect_ips6PortNo;
         } elsif (($i == 2) and ($connect_attempthttp == 1)) {
            $connect_protocol = 'http';
            $connect_port = $connect_httpPortNo;
         } elsif (($i == 3) and ($connect_attempthttp6 == 1)) {
            $DB::single=2 if $opt_debug == 1;
            next unless $opt_soap_lite_v6 == 1;
            $connect_protocol = 'http6';
            $connect_port = $connect_ip6PortNo;
         } else {next;}

         $test_connection = $connect_protocol . "://" . $connect_hostName . ":" . $connect_port . "///cms/soap";
         logit(0,"Trial SOAP connection based index.xml [$test_connection]");
         $oHub = SOAP::Lite->proxy($test_connection,timeout => $opt_soap_timeout);
         $oHub->outputxml('true');
         $oHub->on_fault( sub {});      # pass back all errors
         $connect_res = DoSoap('CT_Get_Object','Local_System_Command');
         $run_status = 0;
         if ($soap_rc == 0) {
            if ($soap_faultstr eq "") {
               logit(0,"SOAP connection success [$test_connection]");
               $connection = $test_connection;
               return 0;
            }
         }
      }  # end of analysis if single index.xml file
   }  # end of attempt to retrieve index files
logit(0,"unable to establish connection to SOAP server");
$run_status++;
}

# History log

# 0.25000  : New script based on Agent Survey 3.40000
# 0.30000  : add retry logic, check for invalid oplog
# 0.60000  : retry defaulted to on, noretry added to turn off
#          : Check for valid number of returned hash entries
