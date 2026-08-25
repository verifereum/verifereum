Theory vfmTest2685[no_sig_docs]
Ancestors vfmTestDefs2685
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2685_0.nsv", "result2685_1.nsv", "result2685_2.nsv", "result2685_3.nsv"];
val thyn = "vfmTestDefs2685";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
