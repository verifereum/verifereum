Theory vfmTest2957[no_sig_docs]
Ancestors vfmTestDefs2957
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2957_0.nsv", "result2957_1.nsv"];
val thyn = "vfmTestDefs2957";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
