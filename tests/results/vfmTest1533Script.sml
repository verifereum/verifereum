Theory vfmTest1533[no_sig_docs]
Ancestors vfmTestDefs1533
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1533_0.nsv", "result1533_1.nsv", "result1533_2.nsv", "result1533_3.nsv"];
val thyn = "vfmTestDefs1533";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
