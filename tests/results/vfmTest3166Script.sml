Theory vfmTest3166[no_sig_docs]
Ancestors vfmTestDefs3166
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3166_0.nsv", "result3166_1.nsv", "result3166_2.nsv", "result3166_3.nsv", "result3166_4.nsv", "result3166_5.nsv", "result3166_6.nsv", "result3166_7.nsv", "result3166_8.nsv", "result3166_9.nsv", "result3166_10.nsv", "result3166_11.nsv", "result3166_12.nsv", "result3166_13.nsv", "result3166_14.nsv", "result3166_15.nsv", "result3166_16.nsv", "result3166_17.nsv", "result3166_18.nsv", "result3166_19.nsv", "result3166_20.nsv", "result3166_21.nsv", "result3166_22.nsv", "result3166_23.nsv", "result3166_24.nsv", "result3166_25.nsv", "result3166_26.nsv", "result3166_27.nsv", "result3166_28.nsv", "result3166_29.nsv", "result3166_30.nsv", "result3166_31.nsv", "result3166_32.nsv", "result3166_33.nsv", "result3166_34.nsv", "result3166_35.nsv"];
val thyn = "vfmTestDefs3166";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
