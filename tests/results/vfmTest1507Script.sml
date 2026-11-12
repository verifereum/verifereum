Theory vfmTest1507[no_sig_docs]
Ancestors vfmTestDefs1507
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1507_0.nsv", "result1507_1.nsv", "result1507_2.nsv", "result1507_3.nsv", "result1507_4.nsv", "result1507_5.nsv", "result1507_6.nsv", "result1507_7.nsv"];
val thyn = "vfmTestDefs1507";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
