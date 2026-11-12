Theory vfmTest0062[no_sig_docs]
Ancestors vfmTestDefs0062
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0062_0.nsv", "result0062_1.nsv", "result0062_2.nsv", "result0062_3.nsv", "result0062_4.nsv", "result0062_5.nsv", "result0062_6.nsv", "result0062_7.nsv"];
val thyn = "vfmTestDefs0062";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
