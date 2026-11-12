Theory vfmTest0267[no_sig_docs]
Ancestors vfmTestDefs0267
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0267_0.nsv", "result0267_1.nsv", "result0267_2.nsv", "result0267_3.nsv", "result0267_4.nsv", "result0267_5.nsv", "result0267_6.nsv", "result0267_7.nsv", "result0267_8.nsv", "result0267_9.nsv", "result0267_10.nsv", "result0267_11.nsv", "result0267_12.nsv", "result0267_13.nsv"];
val thyn = "vfmTestDefs0267";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
