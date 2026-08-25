Theory vfmTest2264[no_sig_docs]
Ancestors vfmTestDefs2264
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2264_0.nsv", "result2264_1.nsv"];
val thyn = "vfmTestDefs2264";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
