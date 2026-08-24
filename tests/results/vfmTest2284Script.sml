Theory vfmTest2284[no_sig_docs]
Ancestors vfmTestDefs2284
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2284_0.nsv", "result2284_1.nsv"];
val thyn = "vfmTestDefs2284";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
