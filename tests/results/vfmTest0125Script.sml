Theory vfmTest0125[no_sig_docs]
Ancestors vfmTestDefs0125
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0125_0.nsv", "result0125_1.nsv", "result0125_2.nsv", "result0125_3.nsv", "result0125_4.nsv", "result0125_5.nsv", "result0125_6.nsv", "result0125_7.nsv", "result0125_8.nsv", "result0125_9.nsv", "result0125_10.nsv", "result0125_11.nsv", "result0125_12.nsv", "result0125_13.nsv", "result0125_14.nsv", "result0125_15.nsv"];
val thyn = "vfmTestDefs0125";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
