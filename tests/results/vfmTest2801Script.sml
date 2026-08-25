Theory vfmTest2801[no_sig_docs]
Ancestors vfmTestDefs2801
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2801_0.nsv", "result2801_1.nsv", "result2801_2.nsv", "result2801_3.nsv"];
val thyn = "vfmTestDefs2801";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
