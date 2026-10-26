Theory vfmTest2944[no_sig_docs]
Ancestors vfmTestDefs2944
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2944_0.nsv", "result2944_1.nsv", "result2944_2.nsv"];
val thyn = "vfmTestDefs2944";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
