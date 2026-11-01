Theory vfmTest2950[no_sig_docs]
Ancestors vfmTestDefs2950
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2950_0.nsv", "result2950_1.nsv", "result2950_2.nsv", "result2950_3.nsv"];
val thyn = "vfmTestDefs2950";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
