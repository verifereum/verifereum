Theory vfmTest0995[no_sig_docs]
Ancestors vfmTestDefs0995
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0995_0.nsv", "result0995_1.nsv", "result0995_2.nsv", "result0995_3.nsv", "result0995_4.nsv", "result0995_5.nsv", "result0995_6.nsv", "result0995_7.nsv", "result0995_8.nsv", "result0995_9.nsv", "result0995_10.nsv", "result0995_11.nsv", "result0995_12.nsv", "result0995_13.nsv", "result0995_14.nsv", "result0995_15.nsv", "result0995_16.nsv", "result0995_17.nsv", "result0995_18.nsv", "result0995_19.nsv", "result0995_20.nsv", "result0995_21.nsv", "result0995_22.nsv", "result0995_23.nsv", "result0995_24.nsv", "result0995_25.nsv", "result0995_26.nsv", "result0995_27.nsv", "result0995_28.nsv", "result0995_29.nsv", "result0995_30.nsv", "result0995_31.nsv", "result0995_32.nsv", "result0995_33.nsv", "result0995_34.nsv", "result0995_35.nsv"];
val thyn = "vfmTestDefs0995";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
