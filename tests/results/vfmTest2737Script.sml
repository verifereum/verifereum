Theory vfmTest2737[no_sig_docs]
Ancestors vfmTestDefs2737
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2737_0.nsv", "result2737_1.nsv", "result2737_2.nsv", "result2737_3.nsv"];
val thyn = "vfmTestDefs2737";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
