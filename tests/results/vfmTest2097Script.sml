Theory vfmTest2097[no_sig_docs]
Ancestors vfmTestDefs2097
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2097_0.nsv", "result2097_1.nsv"];
val thyn = "vfmTestDefs2097";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
