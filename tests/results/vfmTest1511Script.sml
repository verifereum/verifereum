Theory vfmTest1511[no_sig_docs]
Ancestors vfmTestDefs1511
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1511_0.nsv", "result1511_1.nsv", "result1511_2.nsv", "result1511_3.nsv", "result1511_4.nsv", "result1511_5.nsv", "result1511_6.nsv", "result1511_7.nsv", "result1511_8.nsv", "result1511_9.nsv", "result1511_10.nsv", "result1511_11.nsv"];
val thyn = "vfmTestDefs1511";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
