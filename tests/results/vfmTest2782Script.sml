Theory vfmTest2782[no_sig_docs]
Ancestors vfmTestDefs2782
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2782_0.nsv", "result2782_1.nsv", "result2782_2.nsv", "result2782_3.nsv"];
val thyn = "vfmTestDefs2782";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
