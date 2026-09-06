Theory vfmTest2269[no_sig_docs]
Ancestors vfmTestDefs2269
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2269_0.nsv", "result2269_1.nsv", "result2269_2.nsv"];
val thyn = "vfmTestDefs2269";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
