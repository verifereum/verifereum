Theory vfmTest2263[no_sig_docs]
Ancestors vfmTestDefs2263
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2263_0.nsv", "result2263_1.nsv", "result2263_2.nsv", "result2263_3.nsv", "result2263_4.nsv", "result2263_5.nsv", "result2263_6.nsv", "result2263_7.nsv", "result2263_8.nsv", "result2263_9.nsv"];
val thyn = "vfmTestDefs2263";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
