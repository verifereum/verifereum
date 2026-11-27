Theory vfmTest0652[no_sig_docs]
Ancestors vfmTestDefs0652
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0652_0.nsv", "result0652_1.nsv", "result0652_2.nsv", "result0652_3.nsv", "result0652_4.nsv", "result0652_5.nsv", "result0652_6.nsv", "result0652_7.nsv", "result0652_8.nsv", "result0652_9.nsv", "result0652_10.nsv", "result0652_11.nsv", "result0652_12.nsv", "result0652_13.nsv", "result0652_14.nsv", "result0652_15.nsv", "result0652_16.nsv", "result0652_17.nsv", "result0652_18.nsv", "result0652_19.nsv", "result0652_20.nsv", "result0652_21.nsv", "result0652_22.nsv", "result0652_23.nsv", "result0652_24.nsv", "result0652_25.nsv", "result0652_26.nsv", "result0652_27.nsv", "result0652_28.nsv", "result0652_29.nsv", "result0652_30.nsv", "result0652_31.nsv", "result0652_32.nsv", "result0652_33.nsv", "result0652_34.nsv", "result0652_35.nsv"];
val thyn = "vfmTestDefs0652";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
