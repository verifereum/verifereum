Theory vfmTest0666[no_sig_docs]
Ancestors vfmTestDefs0666
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0666_0.nsv", "result0666_1.nsv", "result0666_2.nsv", "result0666_3.nsv", "result0666_4.nsv", "result0666_5.nsv", "result0666_6.nsv", "result0666_7.nsv", "result0666_8.nsv", "result0666_9.nsv", "result0666_10.nsv", "result0666_11.nsv", "result0666_12.nsv", "result0666_13.nsv", "result0666_14.nsv", "result0666_15.nsv", "result0666_16.nsv", "result0666_17.nsv", "result0666_18.nsv", "result0666_19.nsv", "result0666_20.nsv", "result0666_21.nsv", "result0666_22.nsv", "result0666_23.nsv"];
val thyn = "vfmTestDefs0666";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
