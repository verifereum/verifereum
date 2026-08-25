Theory vfmTest2615[no_sig_docs]
Ancestors vfmTestDefs2615
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2615_0.nsv", "result2615_1.nsv", "result2615_2.nsv", "result2615_3.nsv"];
val thyn = "vfmTestDefs2615";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
