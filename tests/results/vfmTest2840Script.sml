Theory vfmTest2840[no_sig_docs]
Ancestors vfmTestDefs2840
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2840_0.nsv", "result2840_1.nsv", "result2840_2.nsv", "result2840_3.nsv"];
val thyn = "vfmTestDefs2840";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
