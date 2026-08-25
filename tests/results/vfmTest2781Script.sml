Theory vfmTest2781[no_sig_docs]
Ancestors vfmTestDefs2781
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2781_0.nsv", "result2781_1.nsv", "result2781_2.nsv", "result2781_3.nsv"];
val thyn = "vfmTestDefs2781";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
