Theory vfmTest1567[no_sig_docs]
Ancestors vfmTestDefs1567
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1567_0.nsv", "result1567_1.nsv", "result1567_2.nsv", "result1567_3.nsv", "result1567_4.nsv", "result1567_5.nsv", "result1567_6.nsv", "result1567_7.nsv", "result1567_8.nsv", "result1567_9.nsv", "result1567_10.nsv", "result1567_11.nsv", "result1567_12.nsv", "result1567_13.nsv", "result1567_14.nsv", "result1567_15.nsv", "result1567_16.nsv", "result1567_17.nsv", "result1567_18.nsv", "result1567_19.nsv"];
val thyn = "vfmTestDefs1567";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
