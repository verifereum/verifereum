Theory vfmTest0104[no_sig_docs]
Ancestors vfmTestDefs0104
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0104_0.nsv", "result0104_1.nsv", "result0104_2.nsv", "result0104_3.nsv", "result0104_4.nsv", "result0104_5.nsv", "result0104_6.nsv", "result0104_7.nsv", "result0104_8.nsv"];
val thyn = "vfmTestDefs0104";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
