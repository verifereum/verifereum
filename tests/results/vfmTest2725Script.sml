Theory vfmTest2725[no_sig_docs]
Ancestors vfmTestDefs2725
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2725_0.nsv", "result2725_1.nsv", "result2725_2.nsv", "result2725_3.nsv"];
val thyn = "vfmTestDefs2725";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
