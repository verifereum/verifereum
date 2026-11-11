Theory vfmTest0421[no_sig_docs]
Ancestors vfmTestDefs0421
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0421_0.nsv", "result0421_1.nsv", "result0421_2.nsv", "result0421_3.nsv", "result0421_4.nsv", "result0421_5.nsv", "result0421_6.nsv", "result0421_7.nsv", "result0421_8.nsv", "result0421_9.nsv", "result0421_10.nsv", "result0421_11.nsv", "result0421_12.nsv", "result0421_13.nsv", "result0421_14.nsv", "result0421_15.nsv", "result0421_16.nsv", "result0421_17.nsv", "result0421_18.nsv", "result0421_19.nsv", "result0421_20.nsv", "result0421_21.nsv", "result0421_22.nsv", "result0421_23.nsv", "result0421_24.nsv", "result0421_25.nsv", "result0421_26.nsv"];
val thyn = "vfmTestDefs0421";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
