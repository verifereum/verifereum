Theory vfmTest0948[no_sig_docs]
Ancestors vfmTestDefs0948
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0948_0.nsv", "result0948_1.nsv", "result0948_2.nsv", "result0948_3.nsv", "result0948_4.nsv", "result0948_5.nsv", "result0948_6.nsv", "result0948_7.nsv", "result0948_8.nsv"];
val thyn = "vfmTestDefs0948";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
