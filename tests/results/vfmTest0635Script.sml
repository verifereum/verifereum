Theory vfmTest0635[no_sig_docs]
Ancestors vfmTestDefs0635
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0635_0.nsv", "result0635_1.nsv", "result0635_2.nsv", "result0635_3.nsv", "result0635_4.nsv", "result0635_5.nsv", "result0635_6.nsv", "result0635_7.nsv", "result0635_8.nsv", "result0635_9.nsv", "result0635_10.nsv", "result0635_11.nsv", "result0635_12.nsv", "result0635_13.nsv", "result0635_14.nsv", "result0635_15.nsv", "result0635_16.nsv", "result0635_17.nsv", "result0635_18.nsv", "result0635_19.nsv", "result0635_20.nsv", "result0635_21.nsv", "result0635_22.nsv", "result0635_23.nsv", "result0635_24.nsv", "result0635_25.nsv", "result0635_26.nsv", "result0635_27.nsv", "result0635_28.nsv", "result0635_29.nsv", "result0635_30.nsv", "result0635_31.nsv", "result0635_32.nsv", "result0635_33.nsv", "result0635_34.nsv", "result0635_35.nsv"];
val thyn = "vfmTestDefs0635";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
