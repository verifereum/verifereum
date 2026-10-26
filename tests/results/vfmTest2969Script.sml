Theory vfmTest2969[no_sig_docs]
Ancestors vfmTestDefs2969
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2969_0.nsv", "result2969_1.nsv", "result2969_2.nsv", "result2969_3.nsv", "result2969_4.nsv", "result2969_5.nsv", "result2969_6.nsv", "result2969_7.nsv", "result2969_8.nsv", "result2969_9.nsv"];
val thyn = "vfmTestDefs2969";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
