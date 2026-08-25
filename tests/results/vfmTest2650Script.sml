Theory vfmTest2650[no_sig_docs]
Ancestors vfmTestDefs2650
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2650_0.nsv", "result2650_1.nsv", "result2650_2.nsv", "result2650_3.nsv"];
val thyn = "vfmTestDefs2650";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
