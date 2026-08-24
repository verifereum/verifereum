Theory vfmTest2709[no_sig_docs]
Ancestors vfmTestDefs2709
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2709_0.nsv", "result2709_1.nsv", "result2709_2.nsv", "result2709_3.nsv"];
val thyn = "vfmTestDefs2709";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
