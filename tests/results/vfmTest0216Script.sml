Theory vfmTest0216[no_sig_docs]
Ancestors vfmTestDefs0216
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0216_0.nsv", "result0216_1.nsv", "result0216_2.nsv", "result0216_3.nsv", "result0216_4.nsv", "result0216_5.nsv", "result0216_6.nsv", "result0216_7.nsv", "result0216_8.nsv", "result0216_9.nsv", "result0216_10.nsv", "result0216_11.nsv", "result0216_12.nsv", "result0216_13.nsv", "result0216_14.nsv", "result0216_15.nsv", "result0216_16.nsv", "result0216_17.nsv", "result0216_18.nsv", "result0216_19.nsv", "result0216_20.nsv", "result0216_21.nsv", "result0216_22.nsv", "result0216_23.nsv", "result0216_24.nsv", "result0216_25.nsv", "result0216_26.nsv", "result0216_27.nsv", "result0216_28.nsv", "result0216_29.nsv", "result0216_30.nsv", "result0216_31.nsv", "result0216_32.nsv", "result0216_33.nsv"];
val thyn = "vfmTestDefs0216";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
