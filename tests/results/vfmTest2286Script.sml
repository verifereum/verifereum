Theory vfmTest2286[no_sig_docs]
Ancestors vfmTestDefs2286
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2286_0.nsv", "result2286_1.nsv", "result2286_2.nsv", "result2286_3.nsv", "result2286_4.nsv", "result2286_5.nsv", "result2286_6.nsv", "result2286_7.nsv"];
val thyn = "vfmTestDefs2286";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
