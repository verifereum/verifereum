Theory vfmTest0203[no_sig_docs]
Ancestors vfmTestDefs0203
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0203_0.nsv", "result0203_1.nsv", "result0203_2.nsv", "result0203_3.nsv", "result0203_4.nsv", "result0203_5.nsv", "result0203_6.nsv", "result0203_7.nsv", "result0203_8.nsv", "result0203_9.nsv", "result0203_10.nsv", "result0203_11.nsv", "result0203_12.nsv", "result0203_13.nsv", "result0203_14.nsv", "result0203_15.nsv", "result0203_16.nsv", "result0203_17.nsv", "result0203_18.nsv", "result0203_19.nsv", "result0203_20.nsv", "result0203_21.nsv", "result0203_22.nsv", "result0203_23.nsv", "result0203_24.nsv", "result0203_25.nsv", "result0203_26.nsv", "result0203_27.nsv", "result0203_28.nsv", "result0203_29.nsv"];
val thyn = "vfmTestDefs0203";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
