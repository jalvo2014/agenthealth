#!/usr/local/bin/perl -w
#------------------------------------------------------------------------------
# Licensed Materials - Property of IBM (C) Copyright IBM Corp. 2010, 2010
# All Rights Reserved US Government Users Restricted Rights - Use, duplication
# or disclosure restricted by GSA ADP Schedule Contract with IBM Corp
#------------------------------------------------------------------------------

#  perl itm_zombie_survey.pl
#
#  Identify agents that are online but not responsive
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

my $gVersion = "0.25000";
my $gWin = (-e "C://") ? 1 : 0;    # 1=Windows, 0=Linux/Unix

BEGIN {
   $ENV{'PERL_NET_HTTPS_SSL_SOCKET_CLASS'} = "Net::SSL";
   $ENV{'PERL_LWP_SSL_VERIFY_HOSTNAME'} = 0;
};   #

use DateTime;                   # Computing with Date Time
use SOAP::Lite;                 # simple SOAP processing. add 'debug' to increase tracing
use HTTP::Request::Common;      #   and HTTP - for SOAP processing
use XML::TreePP;                # parse XML
use Module::Load;               # more flexible
use Data::Dumper;               # debug only

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



my @list = ();
my $rc;
my $node;
my $product;
my $onecmd;
my $oneparm;
my $f;
my $ptx;
my $s_errcode;
my $s_erritem;
my $s_errtext;
my $myargs;
my $survey_sqls = 0;                     # count of SQLs
my $survey_sql_time = 0;                 # record total elapsed time in SQL processing

# forward declarations of subroutines

sub init;                                # read command line and ini file
sub logit;                               # queue one record to survey log
sub dumplog;                             # dump current log to disk file
sub dumplogexit;                         # dump current log to disk file and exit
sub survey_agent;                        # Survey one agent
sub tems_node_analysis;                   # perform analysis of TEMS node status
sub write_stat_report;                   # write statistics report
sub DoSoap;                              # perform a SOAP request and return results
sub survey_error_events;                 # review current ITM events
sub survey_error_files;                  # review current survey error files
sub survey_error_sync;                   # synchronize error files and ITM events
sub survey_error_sync_cmd;               # synchronize error files and produce needed commands
sub survey_error_sync_cmd_send;          # produce error_commands at startup
sub get_timestamp;                       # get current timestatmp
sub calc_timestamp;                      # Add or subtract time from an ITM timestamp
sub get_ITM_epoch;                       # convert from ITM timestamp to epoch seconds
sub datadumperlog;                       # dump a variable using Dump::Data if installed
sub get_connection;                      # get current connection string
sub sitgroup_get_sits;                   # recursive sitgroup exploration

# runtime Statistics variables
my $survey_start_time = time;            # starting time of run
my $survey_runtime;                      # used to calculate current runtime
my $survey_sleeptime = 0;                # record current sleeptime
my $survey_nodes_all;                    # count of known nodes
my $survey_nodes = 0;                    # count of nodes with given product and TEMS
my $survey_nodes_success = 0;            # count of surveyed nodes - success
my $survey_nodes_fail = 0;               # count of surveyed nodes - fail
my $survey_nodes_undone = 0;             # count of surveyed nodes - not yet done
my $survey_nodes_cmd = 0;                # count of Agent commands, some could be errors
my $survey_tems = 0;                     # count of times TEMS surveyed


# option and ini file variables variables

my $opt_log;                    # name of log file
my $opt_ini;                    # name of ini file
my $opt_debuglevel;             # Debug level
my $opt_debug;                  # Debug level
my $opt_h;                      # help file
my $opt_v;                      # verbose flag
my @opt_pc = ();                # Product codes - like ux for Unix OS Agent
my %opt_pcx = ();               # index to Product codes
my @opt_tems = ();              # TEMS names to survey
my %opt_temsx = ();             # index to TEMS names
my $opt_dpr;                    # dump data structure flag
my $opt_std;                    # Credentials from standard input
my $opt_limit;                  # Number of agents to survey before stopping
my $opt_onecycle;               # Perform one full cycle and then stop
my $opt_agent;                  # Review one agent and then stop
my $opt_agent_oplog;            # Get one agent oplog and then stop
my $opt_cmd;                    # A command to execute
my @opt_cmds;                   # A command to execute
my @opt_synch = ();             # synch/duper situations
my %opt_synchx = ();            # synch index
my $synchi = -1;                # number of synch
my @synch = ();                 # synch name
my @synch_sits = ();            # synch situations
my $opt_group_num;              # number of agents to query at one time
my $dx;

my $user="";
my $passwd="";

# Parse control file which contains  operational defaults -
#
my $review_delay;
my @connections = ();               # list of possible hub TEMS servers
my $connection="";
my $history_path = "./";
my $review_delay_success = 604800;  # seven days
my $review_delay_fail    = 86400;   # one day
my $review_delay_nowork  = 300;     # five minutes
my $review_cycle_target  = 60;      # 60 seconds per survey
my $alert_excessive_actions = 0;    # From level 1.10000, option ignored
my $review_survey_timeout = 180;    # how many seconds to wait for a response
my $review_tems_time      = 0;      # time of last TEMS static review
my $review_tems_delay     = 43200;  # delay until next static TEMS review
my $error_situation       =  "";    # Situation used to display error conditions in Portal Client
my $agent_flurry          =  60;    # During of initial stop/start messages after reconnection to TEMS
my $error_cmd             =  "";    # Exit command to communicate error cases
my $error_cmd_startup     = 0;      # Run exit commands at startup for existing error cases

my $cmd;
my $cmd_file;
my $cmd_work;
my $cmd_file_local;
my $cmd_work_local;

$rc = init($args_start);

logit(0,"SURVEY000I - ITM_Zombie_Survey $gVersion $args_start");

# Variables

############
# SOAP Calls
############

# Variables associated directly with SOAP calls and responses
# CPU and Memory
my $sSQL;
my $key;
my $keycmd;
my @log;
my @alog;
my @elog;
my $agent_elog;
my $agent_alog;
my $agent_oplog;
my $survey_count = 0;

# variables for storing Situation Description information from the hub TEMS

my $sx;
my $siti = -1;
my @sitnames     = ();
my %sitnamex     = ();
my @sitobjaccl   = ();
my @situadaccl   = ();
my @sitcmd       = ();
my $incmd;
my $sit;
my $sitrun;

my %objcobj = ();

# variables for storing node and nodelist information from the hub TEMS

my $ssnx;
my $nx;
my $snx;
my $nnx;
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
my @snode_tems_nodelists = ();                 # Managed System Lists the node is included in
my @snode_tems_product = ();                   # Product Code [Agent type] the agent is associated with
my @snode_tems_situations = ();                # list of situations that should be running on the node
my @snode_tems_situation_commands = ();        # list of situation with commands that should be running on the node
my @snode_tems_thrunode = ();                  # thrunode [remote TEMS for simple situations] the agent connects to
my @snode_survey_thrunodes = ();                 # all thrunodes [remote TEMS for simple situations] the agent connects to
my @snode_tems_version = ();                   # version of [remote TEMS for simple situations] the agent connects to
my @snode_tems_hostaddr = ();                  # hostaddr information, include ip address
my @snode_agent_version = ();                  # version  information, include ip address
my @snode_agent_common  = ();                  # common software levels
my @snode_survey_status = ();                  # set to 1 when got good status
my @snode_survey_stamp = ();                   # the local timestamp of last connect to TEMS time
my @snode_survey_time = ();                    # time when survey started
my @snode_survey_time_capture = ();            # epoch when agent time capured
my @snode_survey_time_start = ();              # time when Agent started
my @snode_survey_maxdelay = ();                # maximum time to last situation started
my @snode_survey_maxdelay_situation = ();      # situation started
my @snode_survey_time_skew = ();               # difference between the agent time and TEMS time
my @snode_survey_uptime = ();                  # uptime in seconds
my @snode_survey_connects = ();                # count of connects
my @snode_survey_sitct = ();                   # count of situations running at the node
my @snode_survey_actions = ();                 # count of situation start/stop actions at the node
my @snode_agent_responsive = ();               # when 1, node was responsive
my @snode_agent_interested = ();               # when 1, node is being checked

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
my @tems_os_agent = ();                        # name of OS Agent on the TEMS server
my @tems_os_agent_product = ();                   # OS Agent product type
my @tems_os_agent_thrunode = ();               # OS Agent - TEMS that it is connected to
my $temsat = "";                               # AT clause for SQL to all TEMSes
my $tems_hub_nodeid = "";                      # nodeid of hub;
my $tems_sitgroup = 0;                         # when 1, situation groups on hub TEMS

my $gx;
my $grpi = -1;
my @grp = ();
my %grpx = ();
my @grp_sit = ();
my @grp_grp = ();
my %sum_sits = ();

# variables for getting product information from the node status table

my $prodi = -1;
my @prodnames = ();
my %prodx = ();
my @prodsits = ();
my $px;

# variable used for error_cmd like processing.

my $cmd_agent;
my $cmd_agent_hostaddr;
my $cmd_agent_thrunode;
my $cmd_agent_error;
my $cmd_agent_status;
my $cmd_hub;
my $cmd_survey_hostname;
my $cmd_survey_status;
my $cmd_survey_version;
my $cmd_survey_time;

# variables for tracking error alerts and files

my $ex;
my $error_event_nodei = -1;
my @error_event_node = ();
my %error_event_nodex = ();
my @error_event_item = ();
my @error_event_timestamp = ();
my @error_event_found = ();
my @error_event_deleted = ();

my $error_file_nodei = -1;
my @error_file_node = ();
my %error_file_nodex = ();
my @error_file_item = ();
my @error_file_timestamp = ();
my @error_file_found = ();

my $error_file_prev_nodei = -1;
my @error_file_prev_node = ();
my %error_file_prev_nodex = ();
my @error_file_prev_item = ();
my @error_file_prev_timestamp = ();
my @error_file_prev_found = ();
my @error_file_prev_deleted = ();


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
   $oHub = SOAP::Lite->proxy($connection,timeout => $review_survey_timeout);
   $oHub->outputxml('true');
   $oHub->on_fault( sub {});      # pass back all errors

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
   $sSQL = "SELECT ADDRESS, ANNOT, ENTRTYPE, PORT, PROTOCOL, ORIGINNODE FROM O4SRV.TGBLBRKR AT( '*HUB' ) WHERE ENTRTYPE = 1 AND ORIGINNODE = \'$node\'";
   @list = DoSoap("CT_Get",$sSQL);
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


# static analysis of the TEMS

logit(0,"Survey tems_node_analysis start");
$rc=tems_node_analysis();
logit(0,"Survey tems_node_analysis end");


# At this point we have all the information needed to calculate the situations which
# should be running on the agents in these array slices

$survey_nodes_all = $snodei;

my $ragenti = -1;
my $ragentgi = -1;
my $ragent_low = "";
my $ragent_high = "";
my $in_id;
my $in_datetime;
my $in_node;

foreach $f ( sort { $snode[$snodex{$a}] <=> $snode[$snodex{$b}] } keys %snodex ) {
   my $i = $snodex{$f};
   $ragenti  += 1;
   $ragentgi += 1;
   if ($ragent_low eq "") {
      $ragent_low = $snode[$i];
      $ragent_high = $snode[$i];
   }
   $ragent_low  =  $snode[$i] if $snode[$i] < $ragent_low;
   $ragent_high =  $snode[$i] if $snode[$i] > $ragent_high;
   if ($ragentgi < $opt_group_num) {
      next if $ragenti < $survey_nodes_all;
   }
$DB::single=2;
   # when we get here $ragent_low and $ragent_high bracket the high and low ranges to be surveyed
   $sSQL = "SELECT ID,DATETIME,ORIGINNODE FROM O4SRV.OPLOG '$temsat' WHERE SYSTEM.PARMA('NODELIST','*ALL',4 ) AND ORIGINNODE >= '$ragent_low' AND ORIGINNODE <= '$ragent_high' AND ID='KRALOG000';";
   @list = DoSoap("CT_Get",$sSQL);

$DB::single=2;
   # note errors but continue on
   if ($run_status == 0) {
$DB::single=2;
      if ($#list >= 0) {
$DB::single=2;
         foreach my $r (@list) {
$DB::single=2;
            my $in_id = $r->{ID};
            $in_id =~ s/\s+$//;   #trim trailing whitespace
            $in_datetime = $r->{DATETIME};
            $in_datetime =~ s/\s+$//;   #trim trailing whitespace
##          $originnode = $r->{System_Name};
##          $originnode =~ s/\s+$//;   #trim trailing whitespace
            $in_node = $r->{ORIGINNODE};
            $in_node =~ s/\s+$//;   #trim trailing whitespace
$DB::single=2;
            $sx = $snodex{$in_node};
            next if !defined $sx;
$DB::single=2;
            next if $snode_agent_interested[$i] == 0;
$DB::single=2;
            $snode_agent_responsive[$i] = 1
         }
      }
   }
$DB::single=2;
   #reset group count, low and high bounds
   $ragentgi = -1;
   $ragent_low = "";
   $ragent_high = "";
   last if $ragenti == $survey_nodes_all;
$DB::single=2;
}

$DB::single=2;
my $total_uninterested = 0;
my $total_nonresponsive = 0;
my $total_responsive = 0;
my $rlinei = -1;
my @rline = ();

$DB::single=2;
# now produce report
for (my $i=0; $i<=$snodei; $i++) {
$DB::single=2;
   if ($snode_agent_interested[$i] == 0) {
$DB::single=2;
      $total_uninterested += 1;
   } elsif ($snode_agent_responsive[$i] == 0) {
$DB::single=2;
      $total_nonresponsive += 1;
      $rlinei++;$rline[$rlinei]="$snode[$i],\n";
   } else {
$DB::single=2;
      $total_responsive += 1;
   }
}

$DB::single=2;
print "Zombie Agent Report\n";
print "\n";
print "Total Managed systems,$survey_nodes_all,\n";
print "Total Responsive agents,$total_responsive,\n";
print "Total Zombie agents,$total_nonresponsive,\n";
print "Total Managed systems,$survey_nodes_all,\n";
print "\n";
print "Zombie Agents\n";

$DB::single=2;
for (my $i=0; $i<=$rlinei; $i++) {
$DB::single=2;
   print $rline[$i];
}
$DB::single=2;

dumplogexit;

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
              'group_num=i' => \ $opt_group_num,      # Number of agents to query at one time
              'debug' => \ $opt_debug,                # log file contents control
              'onecycle' => \ $opt_onecycle,          # log file contents control
              'h' => \ $opt_h,                        # help
              'v' => \  $opt_v,                       # verbose - print immediately as well as log
              'pc=s' => \  @opt_pc,                   # Product Code
              'tems=s' => \  @opt_tems,               # TEMS names
              'dpr' => \ $opt_dpr,                    # dump data structures
              'std' => \ $opt_std,                    # credentials from standard input
              'limit=i' => \ $opt_limit,              # limit of surveys
              'cmd=s{1,2}'   => \@opt_cmds,           # Single command to perform
              'agent=s' => \ $opt_agent,              # Single agent survey
              'agent_oplog=s' => \ $opt_agent_oplog   # Single agent oplog
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
   if (!defined $opt_cmd) {$opt_cmd="";}                       # if no command, null it out

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
      my @words = split(" ",$oneline);
      next if $#words == -1;                  # skip blank line
       if ($#words == 0) {                         # single word parameters
         if ($words[0] eq "alert_excessive_actions") {$alert_excessive_actions = 1;}
         elsif ($words[0] eq "debug") {$opt_debug = 1;}
         elsif ($words[0] eq "verbose") {$opt_v = 1;}
         elsif ($words[0] eq "onecycle") {$opt_onecycle = 1;}
         elsif ($words[0] eq "std") {$opt_std = 1;}
         elsif ($words[0] eq "passwd") {}                      # null password
         elsif ($words[0] eq "error_cmd_startup") {$error_cmd_startup = 1;}
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
      elsif ($words[0] eq "limit") {$opt_limit = $words[1];}
      elsif ($words[0] eq "agent") {$opt_agent = $words[1];}
      elsif ($words[0] eq "group_num") {$opt_group_num = $words[1];}
      elsif ($words[0] eq "agent_oplog") {$opt_agent_oplog = $words[1];}
      elsif ($words[0] eq "history_path") {$history_path = $words[1];}
      elsif ($words[0] eq "review_delay_success") {$review_delay_success = $words[1];}
      elsif ($words[0] eq "review_delay_fail") {$review_delay_fail = $words[1];}
      elsif ($words[0] eq "review_delay_nowork") {$review_delay_nowork = $words[1];}
      elsif ($words[0] eq "review_cycle_target") {$review_cycle_target = $words[1];}
      elsif ($words[0] eq "review_survey_timeout") {$review_survey_timeout = $words[1];}
      elsif ($words[0] eq "review_tems_delay") {$review_tems_delay = $words[1];}
      elsif ($words[0] eq "error_situation") {$error_situation = $words[1];}
      elsif ($words[0] eq "error_cmd") {
         shift @words;
         $error_cmd = join(" ",@words);
      }
      elsif ($words[0] eq "synch") {
         $synchi++;
         $opt_synch[$synchi] = $words[1];
         $opt_synchx{$words[1]} = $synchi;
         shift @words;
         shift @words;
         $synch_sits[$synchi] = join(" ",@words);
      }
      elsif ($words[0] eq "agent_flurry") {
         logit(0,"Control agent_flurry ignored - no longer used");
         $agent_flurry = $words[1];
         }
      else {
         logit(0,"SURVEY005E ini file $l - unknown control $words[0]"); # kill process after current phase
         $run_status++;
      }
   }

   # defaults for options not set otherwise

   if (!defined $opt_log) {$opt_log = "zombie.log";}           # default log file if not specified
   if (!defined $opt_h) {$opt_h=0;}                            # help flag
   if (!defined $opt_v) {$opt_v=0;}                            # verbose flag
   if (!defined $opt_onecycle) {$opt_onecycle=0;}              # verbose flag
   if (!defined $opt_limit){$opt_limit=0;}                     # How many nodes to survey
   if (!defined $opt_agent){$opt_agent="";}                    # Single survey agent
   if (!defined $opt_agent_oplog){$opt_agent_oplog="";}        # Single survey oplog capture
   if (!defined $opt_dpr) {$opt_dpr=0;}                        # data dump flag
   if (!defined $opt_std) {$opt_std=0;}                        # default - no credentials in stdin
   if (!defined $opt_group_num) {$opt_group_num=100;}          # default 100 agents queried at a time

   if ($alert_excessive_actions == 1) {
      logit(0,"Control alert_excessive_actions ignored - now controlled in summary process");
   }

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

   $history_path =~ s/\\/\//g;
   $history_path .= "\/" if substr($history_path,length($history_path)-1,1) ne "\/";
   $opt_log = "$history_path" . "$opt_log";
   $cmd_file = $history_path . "zombie.req";
   $cmd_work = $history_path . "zombie.wrk";
   $cmd_file_local = $cmd_file;
   $cmd_work_local = $cmd_work;
   $cmd_file_local =~ s/\//\\/g;
   $cmd_work_local =~ s/\//\\/g;

   $opt_cmd = join(" ",@opt_cmds);
   if ($opt_cmd ne "") {
      if ($gWin == 1) {
         $cmd = "echo $opt_cmd \>\>$cmd_file_local";      # windows flavor of command
      } else {
         $cmd = "echo $opt_cmd \>\>$cmd_file";                  # linux/unix flavor of command
      }
      system($cmd);
      $rc = $?>>8;
      if ($rc != 0) {
         logit(0,"command $cmd failed with exit code $rc - $!");
      }
      dumplog;
      exit 0;
   }
}

write_stat_report;
dumplogexit;

exit 0;


sub tems_node_analysis
{
   $survey_tems++;
   $review_tems_time = time;

   # local variables
   my $node_filebase;


   # reset all variables used by the tems static analysis
   $siti = -1;
   @sitnames     = ();
   %sitnamex     = ();
   @sitobjaccl   = ();
   @situadaccl   = ();
   $sitrun = "";
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
   @snode_tems_nodelists = ();
   @snode_tems_product = ();
   @snode_tems_situations = ();
   @snode_tems_situation_commands = ();
   @snode_tems_thrunode = ();
   @snode_survey_thrunodes = ();
   @snode_tems_version = ();
   @snode_tems_hostaddr = ();
   @snode_agent_version = ();                  # version  information, include ip address
   @snode_agent_common  = ();                  # common software levels
   @snode_survey_status = ();
   @snode_survey_stamp = ();
   @snode_survey_time = ();
   @snode_survey_time_capture = ();
   @snode_survey_time_start = ();
   @snode_survey_maxdelay = ();
   @snode_survey_maxdelay_situation = ();
   @snode_survey_time_skew = ();
   @snode_survey_uptime = ();
   @snode_survey_connects = ();
   @snode_survey_sitct = ();
   @snode_survey_actions = ();
   @snode_agent_responsive = ();               # when 1, node was responsive
   @snode_agent_interested = ();               # when 1, node is being checked

   $temsi = -1;
   @tems = ();
   %temsx = ();
   @tems_thrunode = ();
   @tems_version = ();                         # version
   @tems_vmsize = ();                          # current process size
   @tems_cpubusy = ();                         # current process cpubusy
   @tems_server_busy = ();                     # current server cpubusy
   @tems_hostaddr = ();                        # current TEMS host address
   @tems_os_agent = ();                        # name of OS Agent on the TEMS server
   @tems_os_agent_product = ();                   # OS Agent product type
   @tems_os_agent_thrunode = ();               # OS Agent - tems the agent is connected to
   @tems_time = ();
   @tems_time_epoch = ();
   @tems_time_capture = ();
   $temsat = "";
   $tems_sitgroup = 0;                         # when 1, situation groups on hub TEMS

   # variables for tracking situation groups.

   $grpi = -1;
   @grp = ();
   %grpx = ();
   @grp_sit = ();
   @grp_grp = ();

   # variables for getting product information from the node status table

   $prodi = -1;
   @prodnames = ();
   %prodx = ();
   @prodsits = ();


   # variables for calculating the UADVISOR situations and situations with commands

   my $name;

   # get names of online TEMSes
   $sSQL = "SELECT NODE, THRUNODE, HOSTADDR, VERSION FROM O4SRV.INODESTS WHERE O4ONLINE='Y' AND PRODUCT='EM'";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}

   foreach my $r (@list) {
       $node = $r->{NODE};
       $node =~ s/\s+$//;   #trim trailing whitespace
       $temsi++;
       $tx = $temsi;
       $tems[$tx] = $node;
       $temsx{$node} = $tx;
       my $thrunode = $r->{THRUNODE};
       $thrunode =~ s/\s+$//;   #trim trailing whitespace
       $tems_thrunode[$tx] = $thrunode;
       $tems_version[$tx] = $r->{VERSION};
       my $hostaddr = $r->{HOSTADDR};
       $hostaddr =~ s/\s+$//;   #trim trailing whitespace
       $tems_hub_nodeid = $node if $node eq $thrunode;
       $tems_hostaddr[$tx] = $hostaddr;
       $tems_time[$tx] = 0;
       $tems_time_capture[$tx] = 0;
       $tems_vmsize[$tx] = 0;
       $tems_cpubusy[$tx] = 0;
       $tems_server_busy[$tx] = 0;
       $tems_os_agent[$tx] = "";
       $tems_os_agent_product[$tx] = "";
       $tems_os_agent_thrunode[$tx] = "";
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
     $temsat .= $node . "'";
   }
   $temsat .= ")";

   # get node status for online managed systems

   $sSQL = "SELECT NODE, THRUNODE, PRODUCT, HOSTADDR, VERSION, RESERVED FROM O4SRV.INODESTS WHERE O4ONLINE='Y'";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}

   foreach my $r (@list) {
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
$DB::single=2;
       $ptx = $temsx{$thrunode};    #ignore any agents not connected through TEMSes
       next if !defined $ptx;       # the subnode agents

          $snodei++;
          $snx = $snodei;
          $snode[$snx] = $node;
          $snodex{$node} = $snx;
          $node_filebase = $node;
          $node_filebase =~ s/:/_/g;
          $snode_filex{$node_filebase} = $snx;
          $snode_tems_nodelists[$snx] = "";
          $snode_survey_online[$snx] = 1;                    # node online when we checked the TEMS tables
          $snode_survey_sits[$snx] = " ";
          $snode_persist_sits[$snx] = " ";
          $snode_survey_sits_noauto[$snx] = " ";
          $snode_tems_situations[$snx] = " ";
          $snode_tems_situation_commands[$snx] = " ";
          $snode_tems_product[$snx] = $product;
          $snode_tems_hostaddr[$snx] = $hostaddr;
          $snode_tems_thrunode[$snx] = $thrunode;
          $snode_survey_thrunodes[$snx] = "";
          $snode_agent_version[$snx] = $agent_version;
          $snode_tems_version[$snx] = "";
          $ptx = $temsx{$thrunode};
          $snode_tems_version[$snx] = $tems_version[$ptx] if defined $ptx;
          $snode_agent_common[$snx] = $agent_common;
          $snode_survey_status[$snx] = -1;
          $snode_agent_responsive[$snx] = 0;           # non-responsive until tested
          $snode_agent_interested[$snx] = 1;           # interested unless product values set
$DB::single=2;
          if ($#opt_pc != -1) {                        # if product codes set, only interested in those
$DB::single=2;
             $ptx = $opt_pcx{$product};
$DB::single=2;
             $snode_agent_interested[$snx] = 0 if !defined $ptx;
$DB::single=2;
          }

#??  handle single agent check
#$DB::single=2;
#          if ($opt_agent ne "") {
#$DB::single=2;
#             next if $node ne $opt_agent;
#          }
#$DB::single=2;

       logit(100,"Node $snodei $node product[$snode_tems_product[$snx]] thrunode[[$snode_tems_thrunode[$snx]] hostaddr[[$snode_tems_hostaddr[$snx]]  agent_version[$snode_agent_version[$snx]] tems_version[$snode_tems_version[$snx]] agent_common[$snode_agent_common[$snx]]");
   }

  dumplog;
  @log = ();
}



#------------------------------------------------------------------------------
# Perform soap process
#------------------------------------------------------------------------------
sub DoSoap
{
   my $rt;
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

  This script surveys an ITM environment looking for exceptions such as
  situations not running as expected.

  Default values:
    log          : zombie.log
    ini          : zombie.ini
    user         : <none>
    passwd       : <none>
    debuglevel   : 90 [considerable number of messages]
    debug        : 0  when 1 some breakpoints are enabled]
    onecycle     : 0  survey all agents under current filter and then stop
    h            : 0  display help information
    v            : 0  display log messages on console
    pc           : product code of agents - can supply multiple codes
    tems         : tems the agents report to - can supply multiple code
    dpr          : 0  dump data structure if Dump::Data installed
    std          : 0  get user/password from stardard input
    limit        : 0  stop after this many surveys if positive
    cmd          : <none> single comand to perform
    agent        : <none> single agent survey and then stop
    agent_optlog : <none> capture operations log from single agent and then stop

  Example invovation
    $0  -ini <control file> -pc ux -limit 40

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
      $oHub = SOAP::Lite->proxy($test_connection,timeout => $review_survey_timeout);          # set Soap::Lite controls
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
      $oHub = SOAP::Lite->proxy($test_connection,timeout => $review_survey_timeout);
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
         $oHub = SOAP::Lite->proxy($test_connection,timeout => $review_survey_timeout);
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
