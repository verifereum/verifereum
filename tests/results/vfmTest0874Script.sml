Theory vfmTest0874[no_sig_docs]
Ancestors vfmTestDefs0874
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0874_0.nsv", "result0874_1.nsv", "result0874_2.nsv", "result0874_3.nsv", "result0874_4.nsv", "result0874_5.nsv", "result0874_6.nsv", "result0874_7.nsv", "result0874_8.nsv", "result0874_9.nsv"];
val thyn = "vfmTestDefs0874";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
