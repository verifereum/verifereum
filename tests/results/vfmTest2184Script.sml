Theory vfmTest2184[no_sig_docs]
Ancestors vfmTestDefs2184
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2184_0.nsv", "result2184_1.nsv", "result2184_2.nsv", "result2184_3.nsv", "result2184_4.nsv", "result2184_5.nsv", "result2184_6.nsv", "result2184_7.nsv", "result2184_8.nsv"];
val thyn = "vfmTestDefs2184";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
