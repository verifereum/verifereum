Theory vfmTest1454[no_sig_docs]
Ancestors vfmTestDefs1454
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1454_0.nsv", "result1454_1.nsv", "result1454_2.nsv", "result1454_3.nsv", "result1454_4.nsv", "result1454_5.nsv", "result1454_6.nsv", "result1454_7.nsv", "result1454_8.nsv"];
val thyn = "vfmTestDefs1454";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
