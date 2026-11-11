Theory vfmTest0657[no_sig_docs]
Ancestors vfmTestDefs0657
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0657_0.nsv", "result0657_1.nsv", "result0657_2.nsv", "result0657_3.nsv", "result0657_4.nsv", "result0657_5.nsv", "result0657_6.nsv", "result0657_7.nsv", "result0657_8.nsv", "result0657_9.nsv", "result0657_10.nsv", "result0657_11.nsv", "result0657_12.nsv", "result0657_13.nsv", "result0657_14.nsv", "result0657_15.nsv", "result0657_16.nsv", "result0657_17.nsv", "result0657_18.nsv", "result0657_19.nsv", "result0657_20.nsv", "result0657_21.nsv", "result0657_22.nsv", "result0657_23.nsv", "result0657_24.nsv", "result0657_25.nsv", "result0657_26.nsv", "result0657_27.nsv", "result0657_28.nsv", "result0657_29.nsv", "result0657_30.nsv", "result0657_31.nsv"];
val thyn = "vfmTestDefs0657";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
