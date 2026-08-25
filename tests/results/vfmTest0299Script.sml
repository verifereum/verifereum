Theory vfmTest0299[no_sig_docs]
Ancestors vfmTestDefs0299
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0299_0.nsv", "result0299_1.nsv", "result0299_2.nsv", "result0299_3.nsv", "result0299_4.nsv", "result0299_5.nsv", "result0299_6.nsv", "result0299_7.nsv", "result0299_8.nsv", "result0299_9.nsv", "result0299_10.nsv", "result0299_11.nsv", "result0299_12.nsv", "result0299_13.nsv", "result0299_14.nsv", "result0299_15.nsv", "result0299_16.nsv", "result0299_17.nsv", "result0299_18.nsv", "result0299_19.nsv", "result0299_20.nsv", "result0299_21.nsv", "result0299_22.nsv", "result0299_23.nsv", "result0299_24.nsv", "result0299_25.nsv", "result0299_26.nsv", "result0299_27.nsv", "result0299_28.nsv", "result0299_29.nsv", "result0299_30.nsv", "result0299_31.nsv", "result0299_32.nsv", "result0299_33.nsv", "result0299_34.nsv", "result0299_35.nsv", "result0299_36.nsv", "result0299_37.nsv", "result0299_38.nsv", "result0299_39.nsv", "result0299_40.nsv", "result0299_41.nsv", "result0299_42.nsv", "result0299_43.nsv", "result0299_44.nsv", "result0299_45.nsv", "result0299_46.nsv", "result0299_47.nsv", "result0299_48.nsv", "result0299_49.nsv", "result0299_50.nsv", "result0299_51.nsv", "result0299_52.nsv", "result0299_53.nsv", "result0299_54.nsv", "result0299_55.nsv", "result0299_56.nsv", "result0299_57.nsv", "result0299_58.nsv", "result0299_59.nsv"];
val thyn = "vfmTestDefs0299";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
