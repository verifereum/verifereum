Theory vfmTest0212[no_sig_docs]
Ancestors vfmTestDefs0212
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0212_0.nsv", "result0212_1.nsv", "result0212_2.nsv", "result0212_3.nsv", "result0212_4.nsv", "result0212_5.nsv", "result0212_6.nsv", "result0212_7.nsv", "result0212_8.nsv", "result0212_9.nsv", "result0212_10.nsv", "result0212_11.nsv", "result0212_12.nsv", "result0212_13.nsv", "result0212_14.nsv", "result0212_15.nsv", "result0212_16.nsv", "result0212_17.nsv", "result0212_18.nsv", "result0212_19.nsv", "result0212_20.nsv"];
val thyn = "vfmTestDefs0212";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
