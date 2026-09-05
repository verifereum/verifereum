Theory vfmTest0729[no_sig_docs]
Ancestors vfmTestDefs0729
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0729_0.nsv", "result0729_1.nsv", "result0729_2.nsv", "result0729_3.nsv", "result0729_4.nsv", "result0729_5.nsv", "result0729_6.nsv", "result0729_7.nsv", "result0729_8.nsv", "result0729_9.nsv", "result0729_10.nsv", "result0729_11.nsv", "result0729_12.nsv", "result0729_13.nsv", "result0729_14.nsv", "result0729_15.nsv", "result0729_16.nsv", "result0729_17.nsv", "result0729_18.nsv", "result0729_19.nsv", "result0729_20.nsv", "result0729_21.nsv", "result0729_22.nsv", "result0729_23.nsv", "result0729_24.nsv", "result0729_25.nsv", "result0729_26.nsv", "result0729_27.nsv", "result0729_28.nsv", "result0729_29.nsv", "result0729_30.nsv", "result0729_31.nsv", "result0729_32.nsv", "result0729_33.nsv"];
val thyn = "vfmTestDefs0729";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
