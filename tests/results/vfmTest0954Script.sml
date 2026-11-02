Theory vfmTest0954[no_sig_docs]
Ancestors vfmTestDefs0954
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0954_0.nsv", "result0954_1.nsv", "result0954_2.nsv", "result0954_3.nsv", "result0954_4.nsv", "result0954_5.nsv", "result0954_6.nsv", "result0954_7.nsv", "result0954_8.nsv", "result0954_9.nsv", "result0954_10.nsv", "result0954_11.nsv", "result0954_12.nsv", "result0954_13.nsv", "result0954_14.nsv", "result0954_15.nsv", "result0954_16.nsv", "result0954_17.nsv", "result0954_18.nsv", "result0954_19.nsv", "result0954_20.nsv", "result0954_21.nsv", "result0954_22.nsv", "result0954_23.nsv", "result0954_24.nsv", "result0954_25.nsv", "result0954_26.nsv", "result0954_27.nsv", "result0954_28.nsv", "result0954_29.nsv", "result0954_30.nsv", "result0954_31.nsv", "result0954_32.nsv", "result0954_33.nsv", "result0954_34.nsv"];
val thyn = "vfmTestDefs0954";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
