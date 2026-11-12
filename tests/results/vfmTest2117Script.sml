Theory vfmTest2117[no_sig_docs]
Ancestors vfmTestDefs2117
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2117_0.nsv", "result2117_1.nsv", "result2117_2.nsv", "result2117_3.nsv", "result2117_4.nsv", "result2117_5.nsv", "result2117_6.nsv", "result2117_7.nsv", "result2117_8.nsv"];
val thyn = "vfmTestDefs2117";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
