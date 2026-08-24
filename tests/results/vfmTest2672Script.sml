Theory vfmTest2672[no_sig_docs]
Ancestors vfmTestDefs2672
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2672_0.nsv", "result2672_1.nsv", "result2672_2.nsv"];
val thyn = "vfmTestDefs2672";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
