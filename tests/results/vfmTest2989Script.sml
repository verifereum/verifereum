Theory vfmTest2989[no_sig_docs]
Ancestors vfmTestDefs2989
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2989_0.nsv", "result2989_1.nsv", "result2989_2.nsv", "result2989_3.nsv", "result2989_4.nsv", "result2989_5.nsv", "result2989_6.nsv", "result2989_7.nsv", "result2989_8.nsv", "result2989_9.nsv", "result2989_10.nsv", "result2989_11.nsv", "result2989_12.nsv", "result2989_13.nsv", "result2989_14.nsv", "result2989_15.nsv", "result2989_16.nsv", "result2989_17.nsv", "result2989_18.nsv", "result2989_19.nsv", "result2989_20.nsv", "result2989_21.nsv", "result2989_22.nsv", "result2989_23.nsv", "result2989_24.nsv", "result2989_25.nsv", "result2989_26.nsv", "result2989_27.nsv", "result2989_28.nsv", "result2989_29.nsv", "result2989_30.nsv", "result2989_31.nsv", "result2989_32.nsv", "result2989_33.nsv", "result2989_34.nsv", "result2989_35.nsv", "result2989_36.nsv", "result2989_37.nsv", "result2989_38.nsv", "result2989_39.nsv", "result2989_40.nsv", "result2989_41.nsv", "result2989_42.nsv", "result2989_43.nsv", "result2989_44.nsv", "result2989_45.nsv", "result2989_46.nsv", "result2989_47.nsv", "result2989_48.nsv", "result2989_49.nsv", "result2989_50.nsv", "result2989_51.nsv", "result2989_52.nsv"];
val thyn = "vfmTestDefs2989";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
