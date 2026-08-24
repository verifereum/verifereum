Theory vfmTest2591[no_sig_docs]
Ancestors vfmTestDefs2591
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2591_0.nsv", "result2591_1.nsv", "result2591_2.nsv", "result2591_3.nsv"];
val thyn = "vfmTestDefs2591";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
