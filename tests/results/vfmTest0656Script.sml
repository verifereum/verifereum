Theory vfmTest0656[no_sig_docs]
Ancestors vfmTestDefs0656
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0656_0.nsv", "result0656_1.nsv", "result0656_2.nsv", "result0656_3.nsv", "result0656_4.nsv", "result0656_5.nsv", "result0656_6.nsv", "result0656_7.nsv", "result0656_8.nsv", "result0656_9.nsv", "result0656_10.nsv", "result0656_11.nsv", "result0656_12.nsv", "result0656_13.nsv", "result0656_14.nsv", "result0656_15.nsv", "result0656_16.nsv", "result0656_17.nsv", "result0656_18.nsv", "result0656_19.nsv", "result0656_20.nsv", "result0656_21.nsv", "result0656_22.nsv", "result0656_23.nsv"];
val thyn = "vfmTestDefs0656";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
