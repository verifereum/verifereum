Theory vfmTest2656[no_sig_docs]
Ancestors vfmTestDefs2656
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2656_0.nsv", "result2656_1.nsv", "result2656_2.nsv", "result2656_3.nsv"];
val thyn = "vfmTestDefs2656";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
