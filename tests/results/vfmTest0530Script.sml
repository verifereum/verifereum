Theory vfmTest0530[no_sig_docs]
Ancestors vfmTestDefs0530
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0530_0.nsv", "result0530_1.nsv", "result0530_2.nsv", "result0530_3.nsv", "result0530_4.nsv", "result0530_5.nsv", "result0530_6.nsv", "result0530_7.nsv", "result0530_8.nsv", "result0530_9.nsv", "result0530_10.nsv"];
val thyn = "vfmTestDefs0530";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
