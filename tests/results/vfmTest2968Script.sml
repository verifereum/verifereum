Theory vfmTest2968[no_sig_docs]
Ancestors vfmTestDefs2968
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2968_0.nsv", "result2968_1.nsv", "result2968_2.nsv", "result2968_3.nsv", "result2968_4.nsv", "result2968_5.nsv", "result2968_6.nsv", "result2968_7.nsv", "result2968_8.nsv"];
val thyn = "vfmTestDefs2968";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
