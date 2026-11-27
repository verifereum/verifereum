Theory vfmTest0506[no_sig_docs]
Ancestors vfmTestDefs0506
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0506_0.nsv", "result0506_1.nsv", "result0506_2.nsv", "result0506_3.nsv", "result0506_4.nsv", "result0506_5.nsv", "result0506_6.nsv", "result0506_7.nsv", "result0506_8.nsv", "result0506_9.nsv", "result0506_10.nsv", "result0506_11.nsv", "result0506_12.nsv", "result0506_13.nsv", "result0506_14.nsv", "result0506_15.nsv", "result0506_16.nsv", "result0506_17.nsv", "result0506_18.nsv", "result0506_19.nsv", "result0506_20.nsv", "result0506_21.nsv", "result0506_22.nsv", "result0506_23.nsv"];
val thyn = "vfmTestDefs0506";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
